import Lean
import LeanCondensedMatter
import Lean.Meta.Tactic.Apply

open Lean Elab Command Meta

namespace LeanCondensedMatter.TheoremReplacementAudit

structure Candidate where
  name : Name
  moduleName : Name
  theoremInfo : TheoremVal

structure PreparedCandidate where
  candidate : Candidate
  binderCount : Nat
  resultHead : Option Name
  resultArity : Nat
  argumentHeads : Array (Option Name)

structure ReplacementCandidate where
  name : String
  moduleName : String

structure AuditEntry where
  target : String
  moduleName : String
  proofDependencies : Array String
  probedCandidateCount : Nat
  definitionallyEquivalentTo : Array String
  replacementCandidates : Array ReplacementCandidate

private def maxReplacementCandidatesPerTarget : Nat := 4

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.toString.startsWith "LeanCondensedMatter"

private def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

private def privateDeclarationName? (declName : Name) : Bool :=
  declName.toString.startsWith "_private."

private def containsSubstring (text pattern : String) : Bool :=
  (text.find? pattern).isSome

private def extensionTheoremName? (declName : Name) : Bool :=
  let name := declName.toString
  name.endsWith ".ext" || containsSubstring name ".ext_" || containsSubstring name "_ext_"

private def collectCandidates : CommandElabM (Array Candidate × NameSet) := do
  let env ← getEnv
  let mut candidates := #[]
  let mut theoremNames := NameSet.empty
  for (declName, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    unless (← findDeclarationRanges? declName).isSome do continue
    candidates := candidates.push { name := declName, moduleName, theoremInfo }
    theoremNames := theoremNames.insert declName
  return (candidates, theoremNames)

private def directProjectTheoremDependencyNames
    (projectTheorems : NameSet) (declName : Name) (value : Expr) : Array Name :=
  value.foldConsts #[] fun dependency dependencies =>
    if dependency != declName && projectTheorems.contains dependency &&
        !dependencies.contains dependency then
      dependencies.push dependency
    else
      dependencies

/-- Peel the explicit theorem telescope without reduction. This is only a cheap search filter. -/
private partial def resultShape (binderCount : Nat) : Expr → Nat × Expr
  | .forallE _ _ body _ => resultShape (binderCount + 1) body
  | .mdata _ body => resultShape binderCount body
  | result => (binderCount, result)

private def prepareCandidate (candidate : Candidate) : PreparedCandidate :=
  let (binderCount, result) := resultShape 0 candidate.theoremInfo.type
  let arguments := result.getAppArgs
  {
    candidate
    binderCount
    resultHead := result.getAppFn.constName?
    resultArity := arguments.size
    argumentHeads := arguments.map fun argument => argument.getAppFn.constName?
  }

private def sameArgumentHeadSketch
    (left right : Array (Option Name)) : Bool := Id.run do
  if left.size != right.size then return false
  for i in [:left.size] do
    if left[i]! != right[i]! then return false
  return true

private def compatibleResultShape (source target : PreparedCandidate) : Bool :=
  source.resultHead == target.resultHead && source.resultArity == target.resultArity

private def candidateMap (prepared : Array PreparedCandidate) : NameMap PreparedCandidate :=
  prepared.foldl (init := {}) fun map candidate => map.insert candidate.candidate.name candidate

private def statementDefEq (left right : Candidate) : MetaM Bool :=
  withoutModifyingState do
    withTransparency .reducible do
      let leftConst ← mkConstWithFreshMVarLevels left.name
      let rightConst ← mkConstWithFreshMVarLevels right.name
      isDefEq (← inferType leftConst) (← inferType rightConst)

private def tryCloseGoalWithLocal (goal : MVarId) (locals : Array Expr) : MetaM Bool := do
  let target ← goal.getType'
  for localExpr in locals do
    let saved ← saveState
    if ← isDefEq (← inferType localExpr) target then
      goal.assign localExpr
      return true
    saved.restore
  return false

private def tryCloseGoalWithInstance (goal : MVarId) : MetaM Bool := do
  let target ← goal.getType'
  unless (← isClass? target).isSome do return false
  let saved ← saveState
  try
    let instanceExpr ← synthInstance target
    goal.assign instanceExpr
    return true
  catch _ =>
    saved.restore
    return false

private def closeReplacementSubgoals
    (goals : List MVarId) (locals : Array Expr) : MetaM Bool := do
  let rec loop (pending : List MVarId) : Nat → MetaM Bool
    | 0 => return false
    | fuel + 1 => do
        let pending ← pending.filterM fun goal => return !(← goal.isAssigned)
        if pending.isEmpty then return true
        let mut remaining := []
        let mut progress := false
        for goal in pending do
          if ← tryCloseGoalWithLocal goal locals then
            progress := true
          else if ← tryCloseGoalWithInstance goal then
            progress := true
          else
            remaining := goal :: remaining
        if !progress then return false
        loop remaining.reverse fuel
  loop goals (goals.length + 1)

/-- Check whether an already-used project theorem can discharge the target merely by specialization.
No global theorem search is performed: the source must already occur in the target proof term. -/
private def replacementCloses (source target : Candidate) : MetaM Bool :=
  withoutModifyingState do
    withTransparency .reducible do
      let targetConst ← mkConstWithFreshMVarLevels target.name
      let targetType ← inferType targetConst
      forallTelescopeReducing targetType fun locals targetResult => do
        let goal ← mkFreshExprSyntheticOpaqueMVar targetResult
        try
          let subgoals ← goal.mvarId!.applyConst source.name { allowSynthFailures := true }
          closeReplacementSubgoals subgoals locals
        catch _ =>
          return false

private def auditTarget
    (target : PreparedCandidate)
    (sources : Array PreparedCandidate) :
    MetaM (Array String × Array ReplacementCandidate) := do
  let mut defEq := #[]
  let mut replacements := #[]
  for source in sources do
    let equivalent ←
      if source.binderCount == target.binderCount &&
          sameArgumentHeadSketch source.argumentHeads target.argumentHeads then
        statementDefEq source.candidate target.candidate
      else
        pure false
    if equivalent then
      defEq := defEq.push source.candidate.name.toString
    else if replacements.size < maxReplacementCandidatesPerTarget &&
        (← replacementCloses source.candidate target.candidate) then
      replacements := replacements.push {
        name := source.candidate.name.toString
        moduleName := source.candidate.moduleName.toString
      }
  return (
    defEq.qsort fun left right => left < right,
    replacements.qsort fun left right => left.name < right.name)

private def collectAuditEntries
    (prepared : Array PreparedCandidate) (projectTheorems : NameSet) :
    CommandElabM (Array AuditEntry × Nat) := do
  let byName := candidateMap prepared
  let mut entries := #[]
  let mut totalProbed := 0
  for target in prepared do
    let dependencyNames := directProjectTheoremDependencyNames
      projectTheorems target.candidate.name target.candidate.theoremInfo.value
    let sources := dependencyNames.foldl (init := #[]) fun sources dependency =>
      match byName.find? dependency with
      | none => sources
      | some source =>
          if privateDeclarationName? source.candidate.name ||
              extensionTheoremName? source.candidate.name ||
              !compatibleResultShape source target then
            sources
          else
            sources.push source
    totalProbed := totalProbed + sources.size
    let (defEq, replacements) ←
      if sources.isEmpty then
        pure (#[], #[])
      else
        liftTermElabM <| liftMetaM <| auditTarget target sources
    entries := entries.push {
      target := target.candidate.name.toString
      moduleName := target.candidate.moduleName.toString
      proofDependencies := (dependencyNames.map Name.toString).qsort fun left right => left < right
      probedCandidateCount := sources.size
      definitionallyEquivalentTo := defEq
      replacementCandidates := replacements
    }
  return (
    entries.qsort fun left right => left.target < right.target,
    totalProbed)

private def jsonReplacement (candidate : ReplacementCandidate) : Json :=
  .mkObj [
    ("name", .str candidate.name),
    ("module", .str candidate.moduleName)
  ]

private def jsonEntry (entry : AuditEntry) : Json :=
  .mkObj [
    ("target", .str entry.target),
    ("module", .str entry.moduleName),
    ("proofDependencies", .arr <| entry.proofDependencies.map Json.str),
    ("probedCandidateCount", .num entry.probedCandidateCount),
    ("definitionallyEquivalentTo", .arr <| entry.definitionallyEquivalentTo.map Json.str),
    ("replacementCandidates", .arr <| entry.replacementCandidates.map jsonReplacement)
  ]

private def json (entries : Array AuditEntry) : Json :=
  .arr <| entries.map jsonEntry

run_cmd do
  let (candidates, projectTheorems) ← collectCandidates
  let prepared := candidates.map prepareCandidate
  let (entries, totalProbed) ← collectAuditEntries prepared projectTheorems
  let defEqTargets := entries.filter fun entry => !entry.definitionallyEquivalentTo.isEmpty
  let replacementTargets := entries.filter fun entry => !entry.replacementCandidates.isEmpty
  let replacementEdges := replacementTargets.foldl (init := 0) fun count entry =>
    count + entry.replacementCandidates.size
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorem-replacements.json") (json entries).pretty
  logInfo m!"Generated proof-guided replacement audit for {entries.size} declarations; probed {totalProbed} proof-dependency pairs; {defEqTargets.size} targets have definitionally equivalent proof dependencies; {replacementTargets.size} targets have verified replacements; {replacementEdges} replacement edges"

end LeanCondensedMatter.TheoremReplacementAudit
