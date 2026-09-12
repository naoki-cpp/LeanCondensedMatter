import Lean
import Lake.CLI.Main
import Lake.Load.Toml
import Mathlib.Tactic
import Mathlib.Tactic.TacticAnalysis

open Lean Elab Meta System
open Lean.Meta.Tactic.TryThis
open Parser Tactic

namespace LeanCondensedMatter.ProofRegions

/-- A multi-line tactic sequence that starts from one goal and closes it. -/
structure Region where
  startPos : Position
  endPos : Position
  spanLines : Nat

/-- A concrete replacement found by Lean/Mathlib search and verified by replay. -/
structure Candidate where
  mode : String
  replacement : String
  theoremName? : Option Name := none
  moduleName? : Option Name := none

/-- One proof region together with an optional verified replacement. -/
structure AuditResult where
  region : Region
  candidate? : Option Candidate := none

private def regionOfSeq
    (fileMap : FileMap) (minLines : Nat)
    (seq : Array Mathlib.TacticAnalysis.TacticNode) : Option Region := do
  let first ← seq[0]?
  let last ← seq.back?
  guard (first.tacI.goalsBefore.length == 1)
  guard last.tacI.goalsAfter.isEmpty
  let startRaw ← first.tacI.stx.getPos? true
  let endRaw ← last.tacI.stx.getTailPos? true
  let startPos := fileMap.toPosition startRaw
  let endPos := fileMap.toPosition endRaw
  let spanLines := endPos.line - startPos.line + 1
  guard (spanLines >= minLines)
  return { startPos, endPos, spanLines }

private def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

private partial def containsConst (declName : Name) : Expr → Bool
  | .const name _ => name == declName
  | .app fn arg => containsConst declName fn || containsConst declName arg
  | .lam _ type body _ => containsConst declName type || containsConst declName body
  | .forallE _ type body _ => containsConst declName type || containsConst declName body
  | .letE _ type value body _ =>
      containsConst declName type || containsConst declName value || containsConst declName body
  | .mdata _ body => containsConst declName body
  | .proj _ _ body => containsConst declName body
  | _ => false

private def prettyTactic (stx : TSyntax `tactic) : Command.CommandElabM String := do
  let fmt ← Command.liftCoreM <| Lean.PrettyPrinter.ppTactic ⟨Syntax.stripPos stx⟩
  return fmt.pretty

/-- Replay a concrete tactic and return the proof it assigns to the fresh replay goal. -/
private def replayCandidateProof
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (replacement : TSyntax `tactic) : Command.CommandElabM (Option Expr) := do
  let termCtx ← Command.liftTermElabM read
  let termState ← Command.liftTermElabM get
  node.ctxI.runTactic node.tacI goal fun freshGoal => do
    let goals ← Lean.Elab.runTactic' (ctx := termCtx) (s := termState) freshGoal replacement
    if !goals.isEmpty then
      return none
    return some (← instantiateMVars (mkMVar freshGoal)).headBeta

/--
Accept a replacement only after rerunning its concrete tactic against the original goal and
checking that the resulting proof does not refer to the declaration currently being audited.
The latter matters because offline InfoTree analysis runs after the whole file is elaborated, so a
`@[simp]` theorem can otherwise appear to prove itself during replay.
-/
private def verifiedCandidate
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (mode : String) (replacement : TSyntax `tactic)
    (theoremName? : Option Name := none) (moduleName? : Option Name := none) :
    Command.CommandElabM (Option Candidate) := do
  let savedMessages := (← get).messages
  let proof? ← try
    replayCandidateProof node goal replacement
  catch _ =>
    pure none
  modify fun state => { state with messages := savedMessages }
  let some proof := proof? | return none
  if let some parentDecl := node.ctxI.parentDecl? then
    if containsConst parentDecl proof then
      return none
  return some {
    mode
    replacement := ← prettyTactic replacement
    theoremName?
    moduleName?
  }

/--
Search imported declarations only. This intentionally excludes declarations from the file currently
being audited, including the theorem under construction and declarations that appear later in the
file, so an offline InfoTree cannot create self- or future-reference false positives.
-/
private def importedExactTerm
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) :
    Command.CommandElabM (Option (Term × Name × Name)) :=
  node.ctxI.runTactic node.tacI goal fun freshGoal => freshGoal.withContext do
    let (_, searchGoal) ← freshGoal.intros
    searchGoal.withContext do
      let env ← getEnv
      let candidates ← Lean.Meta.LibrarySearch.librarySearchSymm
        Lean.Meta.LibrarySearch.libSearchFindDecls searchGoal
      let initialState ← saveState
      for ((candidateGoal, candidateMCtx), (declName, modifier)) in candidates do
        let some moduleName := declarationModule? env declName | continue
        setMCtx candidateMCtx
        try
          let thm ← Lean.Meta.LibrarySearch.mkLibrarySearchLemma declName modifier
          let subgoals ← candidateGoal.apply thm { allowSynthFailures := true }
          let remaining ← Lean.Meta.LibrarySearch.solveByElim [] false subgoals 6
          if remaining.isEmpty then
            let proof := (← instantiateMVars (mkMVar freshGoal)).headBeta
            if let some parentDecl := node.ctxI.parentDecl? then
              if containsConst parentDecl proof then
                restoreState initialState
                continue
            let term ← delabToRefinableSyntax proof
            return some (term, declName, moduleName)
        catch _ =>
          pure ()
        restoreState initialState
      return none

/-- Find an imported theorem reuse candidate and verify its concrete `exact` replacement. -/
private def exactSearch
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) :
    Command.CommandElabM (Option Candidate) := do
  let result ← try
    importedExactTerm node goal
  catch _ =>
    pure none
  let some (term, declName, moduleName) := result | return none
  let replacement ← `(tactic| exact $term)
  verifiedCandidate node goal "exact?" replacement (some declName) (some moduleName)

/-- Try a deterministic concrete tactic and retain it only when replay closes the region goal. -/
private def concreteSearch
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (mode : String) (replacement : TSyntax `tactic) : Command.CommandElabM (Option Candidate) :=
  verifiedCandidate node goal mode replacement

private def auditSeq
    (fileMap : FileMap) (minLines : Nat)
    (seq : Array Mathlib.TacticAnalysis.TacticNode) : Command.CommandElabM (Option AuditResult) := do
  let some region := regionOfSeq fileMap minLines seq | return none
  let some first := seq[0]? | return some { region }
  let [goal] := first.tacI.goalsBefore | return some { region }
  if let some candidate ← exactSearch first goal then
    return some { region, candidate? := some candidate }
  if let some candidate ← concreteSearch first goal "simp" (← `(tactic| simp)) then
    return some { region, candidate? := some candidate }
  if let some candidate ← concreteSearch first goal "aesop" (← `(tactic| aesop)) then
    return some { region, candidate? := some candidate }
  return some { region }

private def collectAudits
    (fileMap : FileMap) (minLines : Nat) (trees : Array InfoTree) :
    Command.CommandElabM (Array AuditResult) := do
  let mut results := #[]
  for tree in trees do
    for seq in ← Mathlib.TacticAnalysis.findTacticSeqs tree do
      if let some result ← auditSeq fileMap minLines seq then
        results := results.push result
  return results

private def printErrors (messages : MessageLog) : IO Unit := do
  for msg in messages.toList do
    if msg.severity == .error then
      IO.eprintln (← msg.toString)

private def runAudit
    (inputCtx : Parser.InputContext) (state : Frontend.State) (minLines : Nat) :
    IO (Array AuditResult) := do
  let trees := state.commandState.infoState.trees.toArray
  let action := Frontend.runCommandElabM <| collectAudits inputCtx.fileMap minLines trees
  let (results, _) ← (action.run { inputCtx := inputCtx }).run state
  return results

/-- Read the root package's Lean options directly from `lakefile.toml`. -/
private def loadProjectLeanOptions : IO Options := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <|
    Lake.mkLoadConfig {
      configFile := "lakefile.toml"
      elanInstall?
      leanInstall?
      lakeInstall?
    }
  let some lakefile ← Lake.loadTomlConfig config |>.toBaseIO
    | throw <| IO.userError "failed to load lakefile.toml"
  return (LeanOptions.ofArray lakefile.pkgDecl.config.leanOptions).toOptions

/-- Re-elaborate one Lean source file, extract proof regions, and search for shorter replacements. -/
unsafe def processFile (path : FilePath) (minLines : Nat := 2) : IO Unit := do
  let input ← IO.FS.readFile path
  let options ← loadProjectLeanOptions
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx
  if messages.hasErrors then
    printErrors messages
    throw <| IO.userError "errors while processing imports"

  let env := env.setMainModule (← moduleNameOfFileName path none)
  let commandState := { Command.mkState env messages options with infoState.enabled := true }
  let state ← IO.processCommands inputCtx parserState commandState
  if state.commandState.messages.hasErrors then
    printErrors state.commandState.messages
    throw <| IO.userError "errors while elaborating source file"

  let results ← runAudit inputCtx state minLines
  let candidateCount := results.foldl (init := 0) fun n result =>
    if result.candidate?.isSome then n + 1 else n
  IO.println s!"{path}: {results.size} proof region(s), {candidateCount} verified replacement(s), minimum {minLines} line(s)"
  for result in results do
    let region := result.region
    IO.println s!"  {region.startPos.line}:{region.startPos.column}-{region.endPos.line}:{region.endPos.column} ({region.spanLines} lines)"
    if let some candidate := result.candidate? then
      IO.println s!"    {candidate.mode}: {candidate.replacement}"
      if let some theoremName := candidate.theoremName? then
        IO.println s!"      theorem: {theoremName}"
      if let some moduleName := candidate.moduleName? then
        IO.println s!"      module: {moduleName}"

end LeanCondensedMatter.ProofRegions

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
      LeanCondensedMatter.ProofRegions.processFile ⟨path⟩
  | [path, minLinesText] =>
      let some minLines := minLinesText.toNat? |
        throw <| IO.userError "minimum line count must be a natural number"
      LeanCondensedMatter.ProofRegions.processFile ⟨path⟩ minLines
  | _ =>
      throw <| IO.userError "usage: lake env lean --run scripts/ProofRegions.lean <file.lean> [min-lines]"
