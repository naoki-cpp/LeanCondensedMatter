import Lean
import Lake.CLI.Main
import Lake.Load.Toml
import Mathlib.Tactic
import Mathlib.Tactic.TacticAnalysis
import Mathlib.Tactic.Widget.LibraryRewrite

open Lean Elab Meta System
open Lean.Meta.Tactic.TryThis
open Parser Tactic

namespace LeanCondensedMatter.ProofRegions

/-- A multi-line tactic sequence or subsequence selected for audit. -/
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
  score : Nat := 0
  closesRegion : Bool := true

/-- One proof region together with an optional verified replacement. -/
structure AuditResult where
  region : Region
  candidate? : Option Candidate := none

private structure RewriteSuggestion where
  tactic : TSyntax `tactic
  theoremName : Name
  moduleName : Name
  depth : Nat
  growth : Nat
  introducedConsts : Nat

private structure ExactWitness where
  declName : Name
  moduleName : Name
  modifier : Lean.Meta.LibrarySearch.DeclMod
  symmetric : Bool

private structure ExactSearchCacheEntry where
  shape : Expr
  parentDecl? : Option Name
  result : Option ExactWitness

private def regionOfWindow
    (fileMap : FileMap) (minLines : Nat)
    (seq : Array Mathlib.TacticAnalysis.TacticNode) : Option Region := do
  let first ← seq[0]?
  let last ← seq.back?
  let startRaw ← first.tacI.stx.getPos? true
  let endRaw ← last.tacI.stx.getTailPos? true
  let startPos := fileMap.toPosition startRaw
  let endPos := fileMap.toPosition endRaw
  let spanLines := endPos.line - startPos.line + 1
  guard (spanLines >= minLines)
  return { startPos, endPos, spanLines }

private def regionOfSeq
    (fileMap : FileMap) (minLines : Nat)
    (seq : Array Mathlib.TacticAnalysis.TacticNode) : Option Region := do
  let region ← regionOfWindow fileMap minLines seq
  let first ← seq[0]?
  let last ← seq.back?
  guard (first.tacI.goalsBefore.length == 1)
  guard last.tacI.goalsAfter.isEmpty
  return region

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

private partial def exprSize : Expr → Nat
  | .app fn arg => 1 + exprSize fn + exprSize arg
  | .lam _ type body _ => 1 + exprSize type + exprSize body
  | .forallE _ type body _ => 1 + exprSize type + exprSize body
  | .letE _ type value body _ => 1 + exprSize type + exprSize value + exprSize body
  | .mdata _ body => 1 + exprSize body
  | .proj _ _ body => 1 + exprSize body
  | _ => 1

private partial def exprConsts : Expr → List Name
  | .const name _ => [name]
  | .app fn arg => exprConsts fn ++ exprConsts arg
  | .lam _ type body _ => exprConsts type ++ exprConsts body
  | .forallE _ type body _ => exprConsts type ++ exprConsts body
  | .letE _ type value body _ => exprConsts type ++ exprConsts value ++ exprConsts body
  | .mdata _ body => exprConsts body
  | .proj name _ body => name :: exprConsts body
  | _ => []

private def introducedConstCount (before after : Expr) : Nat :=
  let beforeNames := (exprConsts before).eraseDups
  let afterNames := (exprConsts after).eraseDups
  (afterNames.filter fun name => !beforeNames.contains name).length

private partial def rewriteTargets
    (target : Expr) (fuel : Nat) (depth : Nat := 0) : Array (Expr × Nat) :=
  match fuel with
  | 0 => #[(target, depth)]
  | fuel + 1 =>
      target.getAppArgs.foldl (init := #[(target, depth)]) fun targets arg =>
        targets ++ rewriteTargets arg fuel (depth + 1)

private def localFVarIds (lctx : LocalContext) : List FVarId :=
  lctx.decls.toList.filterMap id |>.map (·.fvarId)

private partial def eraseBinderNames : Expr → Expr
  | .app fn arg => .app (eraseBinderNames fn) (eraseBinderNames arg)
  | .lam _ type body bi =>
      .lam Name.anonymous (eraseBinderNames type) (eraseBinderNames body) bi
  | .forallE _ type body bi =>
      .forallE Name.anonymous (eraseBinderNames type) (eraseBinderNames body) bi
  | .letE _ type value body nonDep =>
      .letE Name.anonymous (eraseBinderNames type) (eraseBinderNames value)
        (eraseBinderNames body) nonDep
  | .mdata _ body => eraseBinderNames body
  | .proj name idx body => .proj name idx (eraseBinderNames body)
  | expr => expr

/-- Close a goal over its local context and erase binder names to obtain an alpha-stable key. -/
private def exactGoalShape (goal : MVarId) : MetaM Expr := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let fvars := ((localFVarIds (← getLCtx)).map mkFVar).toArray
  let closed ← mkForallFVars fvars target
  return eraseBinderNames closed

private def prettyTactic (stx : TSyntax `tactic) : Command.CommandElabM String := do
  let fmt ← Command.liftCoreM <| Lean.PrettyPrinter.ppTactic ⟨Syntax.stripPos stx⟩
  return fmt.pretty

private def tacticSeqText
    (seq : Array Mathlib.TacticAnalysis.TacticNode) : Command.CommandElabM String := do
  let mut text := ""
  for node in seq do
    let tactic : TSyntax `tactic := ⟨node.tacI.stx⟩
    text := text ++ "\n" ++ (← prettyTactic tactic)
  return text

private def theoremMentioned (source : String) (name : Name) : Bool :=
  let shortName := match name with
    | .str _ value => value
    | _ => name.toString
  source.contains name.toString || source.contains shortName

private def theoremMentionBonus (source : String) (name : Name) : Nat :=
  if theoremMentioned source name then 320 else 0

private def candidateBaseScore (spanLines : Nat) : Nat := spanLines * 100

private def rewriteRecommendationFloor (spanLines : Nat) : Nat :=
  candidateBaseScore spanLines + 100

private def rewriteBonus (depth : Nat) : Nat :=
  match depth with
  | 0 => 220
  | 1 => 160
  | _ => 90

private def rewritePenalty (suggestion : RewriteSuggestion) : Nat :=
  Nat.min 220 (suggestion.growth * 6 + suggestion.introducedConsts * 35)

private def isConservativeRewrite (suggestion : RewriteSuggestion) : Bool :=
  suggestion.depth == 0 && suggestion.growth == 0 && suggestion.introducedConsts == 0

private def assumptionPenalty (source : String) (suggestion : RewriteSuggestion) : Nat :=
  if theoremMentioned source suggestion.theoremName then
    20
  else if isConservativeRewrite suggestion then
    140
  else
    420

private def rewriteScore
    (spanLines : Nat) (source : String) (suggestion : RewriteSuggestion)
    (needsAssumption : Bool) : Nat :=
  let reward := candidateBaseScore spanLines + rewriteBonus suggestion.depth +
    theoremMentionBonus source suggestion.theoremName + (if needsAssumption then 15 else 40)
  let penalty := rewritePenalty suggestion +
    (if needsAssumption then assumptionPenalty source suggestion else 0)
  reward - penalty

private def betterCandidate (best : Option Candidate) (candidate : Candidate) : Option Candidate :=
  match best with
  | none => some candidate
  | some current =>
      if candidate.score > current.score ||
          (candidate.score == current.score && candidate.replacement.length < current.replacement.length) then
        some candidate
      else
        best

private def topRewriteSuggestions
    (suggestions : Array RewriteSuggestion) (spanLines : Nat) (source : String)
    (limit : Nat) : Array RewriteSuggestion :=
  let ranked := suggestions.qsort fun a b =>
    decide (rewriteScore spanLines source a false > rewriteScore spanLines source b false)
  ranked.extract 0 (Nat.min limit ranked.size)

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
Replay a concrete tactic and check that it reproduces the goal at the end of an original
intermediate proof region. This is deliberately restricted to one remaining goal; callers also
require the local context to be unchanged across the original region.
-/
private def replayCandidateTransition
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (replacement : TSyntax `tactic) (targetType : Expr) : Command.CommandElabM Bool := do
  let termCtx ← Command.liftTermElabM read
  let termState ← Command.liftTermElabM get
  node.ctxI.runTactic node.tacI goal fun freshGoal => do
    let goals ← Lean.Elab.runTactic' (ctx := termCtx) (s := termState) freshGoal replacement
    let [nextGoal] := goals | return false
    nextGoal.withContext do
      let nextType ← instantiateMVars (← nextGoal.getType)
      return ← isDefEq nextType targetType

/--
Accept a replacement only after rerunning its concrete tactic against the original goal and
checking that the resulting proof does not refer to the declaration currently being audited.
The latter matters because offline InfoTree analysis runs after the whole file is elaborated, so a
`@[simp]` theorem can otherwise appear to prove itself during replay.
-/
private def verifiedCandidate
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (mode : String) (replacement : TSyntax `tactic) (score : Nat)
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
  let replacementText ← prettyTactic replacement
  let lengthPenalty := Nat.min 40 (replacementText.length / 10)
  return some {
    mode
    replacement := replacementText
    theoremName?
    moduleName?
    score := score - lengthPenalty
  }

/-- Accept a one-goal transition replacement after replay reaches the original end-goal type. -/
private def verifiedTransitionCandidate
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) (targetType : Expr)
    (mode : String) (replacement : TSyntax `tactic) (score : Nat)
    (theoremName? : Option Name := none) (moduleName? : Option Name := none) :
    Command.CommandElabM (Option Candidate) := do
  let savedMessages := (← get).messages
  let ok ← try
    replayCandidateTransition node goal replacement targetType
  catch _ =>
    pure false
  modify fun state => { state with messages := savedMessages }
  if !ok then
    return none
  let replacementText ← prettyTactic replacement
  let lengthPenalty := Nat.min 40 (replacementText.length / 10)
  return some {
    mode
    replacement := replacementText
    theoremName?
    moduleName?
    score := score - lengthPenalty
    closesRegion := false
  }

/-- Re-run one cached imported theorem witness against the current goal. -/
private def exactTermFromWitness
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) (witness : ExactWitness) :
    Command.CommandElabM (Option (Term × Name × Name)) :=
  node.ctxI.runTactic node.tacI goal fun freshGoal => freshGoal.withContext do
    let (_, searchGoal) ← freshGoal.intros
    searchGoal.withContext do
      let initialState ← saveState
      try
        let candidateGoal ← if witness.symmetric then
          let some symmGoal ← observing? searchGoal.applySymm | return none
          pure symmGoal
        else
          pure searchGoal
        let thm ← Lean.Meta.LibrarySearch.mkLibrarySearchLemma witness.declName witness.modifier
        let subgoals ← candidateGoal.apply thm { allowSynthFailures := true }
        let remaining ← Lean.Meta.LibrarySearch.solveByElim [] false subgoals 6
        if !remaining.isEmpty then
          restoreState initialState
          return none
        let proof := (← instantiateMVars (mkMVar freshGoal)).headBeta
        if let some parentDecl := node.ctxI.parentDecl? then
          if containsConst parentDecl proof then
            restoreState initialState
            return none
        let term ← delabToRefinableSyntax proof
        return some (term, witness.declName, witness.moduleName)
      catch _ =>
        restoreState initialState
        return none

/--
Search imported declarations only. This intentionally excludes declarations from the file currently
being audited, including the theorem under construction and declarations that appear later in the
file, so an offline InfoTree cannot create self- or future-reference false positives.
-/
private def importedExactTerm
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) :
    Command.CommandElabM (Option (Term × ExactWitness)) :=
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
            let witness := {
              declName
              moduleName
              modifier
              symmetric := candidateGoal != searchGoal
            }
            return some (term, witness)
        catch _ =>
          pure ()
        restoreState initialState
      return none

/-- Cache exact-search outcomes for alpha-equivalent goals, replaying positive witnesses on hits. -/
private def cachedImportedExactTerm
    (cache : IO.Ref (Array ExactSearchCacheEntry))
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) :
    Command.CommandElabM (Option (Term × Name × Name)) := do
  let shape ← node.ctxI.runTactic node.tacI goal fun freshGoal => freshGoal.withContext do
    let (_, searchGoal) ← freshGoal.intros
    exactGoalShape searchGoal
  let entries ← Command.liftIO cache.get
  let parentDecl? := node.ctxI.parentDecl?
  let scoped? := entries.find? fun entry =>
    entry.shape == shape && entry.parentDecl? == parentDecl?
  let reusable? := match scoped? with
    | some entry => some entry
    | none => entries.find? fun entry =>
        entry.shape == shape && entry.result.isSome
  if let some entry := reusable? then
    match entry.result with
    | none => return none
    | some witness =>
        if let some result ← exactTermFromWitness node goal witness then
          return some result
  let result ← try
    importedExactTerm node goal
  catch _ =>
    pure none
  let witness? := result.map (·.2)
  let updated := entries.filter fun entry =>
    !(entry.shape == shape && entry.parentDecl? == parentDecl?)
  Command.liftIO <| cache.set (updated.push { shape, parentDecl?, result := witness? })
  return result.map fun (term, witness) => (term, witness.declName, witness.moduleName)

/-- Find an imported theorem reuse candidate and verify its concrete `exact` replacement. -/
private def exactSearch
    (cache : IO.Ref (Array ExactSearchCacheEntry))
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) (spanLines : Nat)
    (source : String) : Command.CommandElabM (Option Candidate) := do
  let result ← cachedImportedExactTerm cache node goal
  let some (term, declName, moduleName) := result | return none
  let replacement ← `(tactic| exact $term)
  let score := candidateBaseScore spanLines + 140 + theoremMentionBonus source declName
  verifiedCandidate node goal "exact?" replacement score (some declName) (some moduleName)

/--
Collect a bounded set of imported-library rewrites that apply to the goal or one of its shallow
subexpressions. The actual replacement is still accepted only after replay, so this search broadens
discovery without weakening verification.
-/
private def importedRewriteSuggestions
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (maxDepth : Nat := 2) (limit : Nat := 64) :
    Command.CommandElabM (Array RewriteSuggestion) :=
  node.ctxI.runTactic node.tacI goal fun freshGoal => freshGoal.withContext do
    let env ← getEnv
    let target ← freshGoal.getType
    let mut suggestions := #[]
    for (expr, depth) in rewriteTargets target maxDepth do
      for rewrites in ← Mathlib.Tactic.LibraryRewrite.getImportRewrites expr do
        for (rw, declName) in rewrites do
          if suggestions.size >= limit then
            return suggestions
          let some moduleName := declarationModule? env declName | continue
          if !rw.extraGoals.isEmpty then
            continue
          let tactic ← Mathlib.Tactic.LibraryRewrite.tacticSyntax rw none none
          let beforeSize := exprSize expr
          let afterSize := exprSize rw.replacement
          suggestions := suggestions.push {
            tactic
            theoremName := declName
            moduleName
            depth
            growth := afterSize - beforeSize
            introducedConsts := introducedConstCount expr rw.replacement
          }
    return suggestions

/--
Rank rewrites cheaply first, then replay only high-scoring suggestions. Rewrites already named by
the original proof receive a strong relevance bonus. Rewrites that need `assumption` are trusted when
the proof already names the theorem, tolerated when they preserve the root expression shape, and
heavily penalized when they introduce a semantic detour. Weak rewrite recommendations are discarded
so theorem search and deterministic automation can remain the fallback.
-/
private def rewriteSearch
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) (spanLines : Nat)
    (source : String) : Command.CommandElabM (Option Candidate) := do
  let suggestions ← try
    importedRewriteSuggestions node goal
  catch _ =>
    pure #[]
  let suggestions := topRewriteSuggestions suggestions spanLines source 12
  let floor := rewriteRecommendationFloor spanLines
  let mut best : Option Candidate := none
  for suggestion in suggestions do
    let directScore := rewriteScore spanLines source suggestion false
    if directScore >= floor then
      if let some candidate ← verifiedCandidate node goal "rw?" suggestion.tactic directScore
          (some suggestion.theoremName) (some suggestion.moduleName) then
        best := betterCandidate best candidate
    let assumptionScore := rewriteScore spanLines source suggestion true
    if assumptionScore >= floor then
      let rewrite := suggestion.tactic
      let replacement ← `(tactic| $rewrite <;> assumption)
      if let some candidate ← verifiedCandidate node goal "rw?" replacement assumptionScore
          (some suggestion.theoremName) (some suggestion.moduleName) then
        best := betterCandidate best candidate
  return best

/-- Search a pre-ranked rewrite set for one theorem that reproduces an intermediate transition. -/
private def rewriteTransitionSearch
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId) (targetType : Expr)
    (spanLines : Nat) (source : String) (suggestions : Array RewriteSuggestion) :
    Command.CommandElabM (Option Candidate) := do
  let suggestions := suggestions.filter fun suggestion =>
    theoremMentioned source suggestion.theoremName || isConservativeRewrite suggestion
  let suggestions := topRewriteSuggestions suggestions spanLines source 8
  let floor := rewriteRecommendationFloor spanLines
  let mut best : Option Candidate := none
  for suggestion in suggestions do
    let score := rewriteScore spanLines source suggestion false
    if score < floor then
      continue
    if let some candidate ← verifiedTransitionCandidate node goal targetType "rw→" suggestion.tactic
        score (some suggestion.theoremName) (some suggestion.moduleName) then
      best := betterCandidate best candidate
  return best

/-- Try a deterministic concrete tactic and retain it only when replay closes the region goal. -/
private def concreteSearch
    (node : Mathlib.TacticAnalysis.TacticNode) (goal : MVarId)
    (mode : String) (replacement : TSyntax `tactic) (score : Nat) :
    Command.CommandElabM (Option Candidate) :=
  verifiedCandidate node goal mode replacement score

private def auditSeq
    (exactCache : IO.Ref (Array ExactSearchCacheEntry))
    (fileMap : FileMap) (minLines : Nat)
    (seq : Array Mathlib.TacticAnalysis.TacticNode) : Command.CommandElabM (Option AuditResult) := do
  let some region := regionOfSeq fileMap minLines seq | return none
  let some first := seq[0]? | return some { region }
  let [goal] := first.tacI.goalsBefore | return some { region }
  let source ← tacticSeqText seq
  let mut best : Option Candidate := none
  if let some candidate ← rewriteSearch first goal region.spanLines source then
    best := betterCandidate best candidate
  if let some candidate ← exactSearch exactCache first goal region.spanLines source then
    best := betterCandidate best candidate
  if let some candidate ← concreteSearch first goal "simp" (← `(tactic| simp))
      (candidateBaseScore region.spanLines + 100) then
    best := betterCandidate best candidate
  if let some candidate ← concreteSearch first goal "aesop" (← `(tactic| aesop))
      (candidateBaseScore region.spanLines + 50) then
    best := betterCandidate best candidate
  return some { region, candidate? := best }

private def transitionStartEligible
    (node : Mathlib.TacticAnalysis.TacticNode) : Command.CommandElabM Bool := do
  let [goal] := node.tacI.goalsBefore | return false
  let [nextGoal] := node.tacI.goalsAfter | return false
  let some startDecl := node.tacI.mctxBefore.decls.find? goal | return false
  let some nextDecl := node.tacI.mctxAfter.decls.find? nextGoal | return false
  if localFVarIds startDecl.lctx != localFVarIds nextDecl.lctx then
    return false
  let tactic : TSyntax `tactic := ⟨node.tacI.stx⟩
  let text ← prettyTactic tactic
  return text.startsWith "rw " || text.startsWith "simp " || text.startsWith "simpa " ||
    text.startsWith "change " || text.startsWith "nth_rw " || text.startsWith "erw "

/--
Audit a nonterminal tactic window conservatively. The window must start and end with one goal,
retain exactly the same local free variables, and end in a target with no expression metavariables.
Only named imported rewrites are considered for these intermediate transitions.
-/
private def auditTransitionWindow
    (fileMap : FileMap) (minLines : Nat)
    (seq : Array Mathlib.TacticAnalysis.TacticNode) (suggestions : Array RewriteSuggestion) :
    Command.CommandElabM (Option AuditResult) := do
  let some region := regionOfWindow fileMap minLines seq | return none
  let some first := seq[0]? | return none
  let some last := seq.back? | return none
  let [goal] := first.tacI.goalsBefore | return none
  let [endGoal] := last.tacI.goalsAfter | return none
  let some startDecl := first.tacI.mctxBefore.decls.find? goal | return none
  let some endDecl := last.tacI.mctxAfter.decls.find? endGoal | return none
  if localFVarIds startDecl.lctx != localFVarIds endDecl.lctx then
    return none
  if endDecl.type.hasExprMVar then
    return none
  let source ← tacticSeqText seq
  let candidate? ← rewriteTransitionSearch first goal endDecl.type region.spanLines source suggestions
  let some candidate := candidate? | return none
  return some { region, candidate? := some candidate }

private def collectAudits
    (fileMap : FileMap) (minLines : Nat) (trees : Array InfoTree) :
    Command.CommandElabM (Array AuditResult) := do
  let exactCache ← Command.liftIO <| IO.mkRef (#[] : Array ExactSearchCacheEntry)
  let mut results := #[]
  for tree in trees do
    for seq in ← Mathlib.TacticAnalysis.findTacticSeqs tree do
      if let some result ← auditSeq exactCache fileMap minLines seq then
        results := results.push result
      for start in [:seq.size] do
        let maxLen := Nat.min 6 (seq.size - start)
        if maxLen < 2 then
          continue
        let some first := seq[start]? | continue
        if !(← transitionStartEligible first) then
          continue
        let [goal] := first.tacI.goalsBefore | continue
        let suggestions ← try
          importedRewriteSuggestions first goal 1 32
        catch _ =>
          pure #[]
        if suggestions.isEmpty then
          continue
        for offset in [:maxLen] do
          let len := offset + 1
          if len < 2 then
            continue
          let window := seq.extract start (start + len)
          if let some result ← auditTransitionWindow fileMap minLines window suggestions then
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
  let terminalRegionCount := results.foldl (init := 0) fun n result =>
    match result.candidate? with
    | some candidate => if candidate.closesRegion then n + 1 else n
    | none => n + 1
  let closureCandidateCount := results.foldl (init := 0) fun n result =>
    match result.candidate? with
    | some candidate => if candidate.closesRegion then n + 1 else n
    | none => n
  let transitionCandidateCount := results.foldl (init := 0) fun n result =>
    match result.candidate? with
    | some candidate => if candidate.closesRegion then n else n + 1
    | none => n
  let ranked := results.filterMap fun result =>
    result.candidate?.map fun candidate => (result.region, candidate)
  let ranked := ranked.qsort fun a b => decide (a.2.score > b.2.score)

  IO.println s!"{path}: {terminalRegionCount} terminal proof region(s), {closureCandidateCount} closure candidate(s), {transitionCandidateCount} intermediate transition candidate(s), minimum {minLines} line(s)"
  for (region, candidate) in ranked do
    IO.println s!"  score {candidate.score} | {region.startPos.line}:{region.startPos.column}-{region.endPos.line}:{region.endPos.column} ({region.spanLines} lines)"
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
