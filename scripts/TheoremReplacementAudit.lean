import Lean
import LeanCondensedMatter

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
  candidatePoolSize : Nat
  probedCandidateCount : Nat
  candidatePoolTruncated : Bool
  definitionallyEquivalentTo : Array String
  replacementCandidates : Array ReplacementCandidate

private def sourceProbeLimit : Nat := 8
private def maxReplacementCandidatesPerTarget : Nat := 3
private def extraSourceBinderLimit : Nat := 8

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

private def collectDirectDependencyMap
    (candidates : Array Candidate) (projectTheorems : NameSet) : NameMap (Array Name) :=
  candidates.foldl (init := {}) fun dependencies candidate =>
    dependencies.insert candidate.name <|
      directProjectTheoremDependencyNames
        projectTheorems candidate.name candidate.theoremInfo.value

/-- Peel the explicit theorem telescope without invoking reduction. This is deliberately structural:
its job is only to partition the candidate space before any Meta-level replay. -/
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

private def prepareCandidates (candidates : Array Candidate) : Array PreparedCandidate :=
  candidates.map prepareCandidate

private def coarseFingerprint (candidate : PreparedCandidate) : String :=
  let head := candidate.resultHead.map (·.toString) |>.getD "<none>"
  head ++ "#" ++ toString candidate.resultArity

private def candidateBuckets
    (prepared : Array PreparedCandidate) : Std.HashMap String (Array PreparedCandidate) := Id.run do
  let mut buckets : Std.HashMap String (Array PreparedCandidate) := {}
  for candidate in prepared do
    let key := coarseFingerprint candidate
    let bucket := (buckets.get? key).getD #[]
    buckets := buckets.insert key (bucket.push candidate)
  return buckets

private def sameArgumentHeadSketch
    (left right : Array (Option Name)) : Bool := Id.run do
  if left.size != right.size then return false
  for i in [:left.size] do
    if left[i]! != right[i]! then return false
  return true

private def compatibleArgumentHeadSketch
    (source target : Array (Option Name)) : Bool := Id.run do
  if source.size != target.size then return false
  for i in [:source.size] do
    match source[i]!, target[i]! with
    | some sourceHead, some targetHead =>
        if sourceHead != targetHead then return false
    | _, _ => pure ()
  return true

private def rigidMatchCount
    (source target : Array (Option Name)) : Nat := Id.run do
  let mut count := 0
  for i in [:source.size] do
    match source[i]!, target[i]! with
    | some sourceHead, some targetHead =>
        if sourceHead == targetHead then count := count + 1
    | _, _ => pure ()
  return count

private def candidateScore (source target : PreparedCandidate) : Nat :=
  let rigidScore := 4 * rigidMatchCount source.argumentHeads target.argumentHeads
  let sameModuleScore := if source.candidate.moduleName == target.candidate.moduleName then 8 else 0
  let sameNamespaceScore :=
    if source.candidate.name.getPrefix == target.candidate.name.getPrefix then 4 else 0
  let binderScore := if source.binderCount <= target.binderCount then 2 else 0
  rigidScore + sameModuleScore + sameNamespaceScore + binderScore

private def takeFirst (entries : Array α) (limit : Nat) : Array α :=
  entries.foldl (init := #[]) fun taken entry =>
    if taken.size < limit then taken.push entry else taken

private def betterCandidate
    (left right : Nat × PreparedCandidate) : Bool :=
  if left.1 == right.1 then
    left.2.candidate.name.toString < right.2.candidate.name.toString
  else
    left.1 > right.1

/-- Scan the coarse bucket once, but keep only the best bounded set instead of sorting the entire
bucket for every target. The returned pool size makes truncation explicit in generated data. -/
private def selectSources
    (bucket : Array PreparedCandidate) (target : PreparedCandidate) :
    Nat × Array PreparedCandidate := Id.run do
  let mut poolSize := 0
  let mut best : Array (Nat × PreparedCandidate) := #[]
  for source in bucket do
    if source.candidate.name == target.candidate.name ||
        privateDeclarationName? source.candidate.name ||
        extensionTheoremName? source.candidate.name ||
        source.binderCount > target.binderCount + extraSourceBinderLimit ||
        !compatibleArgumentHeadSketch source.argumentHeads target.argumentHeads then
      continue
    poolSize := poolSize + 1
    let ranked := (best.push (candidateScore source target, source)).qsort betterCandidate
    best := takeFirst ranked sourceProbeLimit
  return (poolSize, best.map fun pair => pair.2)

private def statementDefEq (left right : Candidate) : MetaM Bool :=
  withoutModifyingState do
    withTransparency .reducible do
      let leftConst ← mkConstWithFreshMVarLevels left.name
      let rightConst ← mkConstWithFreshMVarLevels right.name
      isDefEq (← inferType leftConst) (← inferType rightConst)

private partial def instantiateSourceBinders
    (type : Expr) (mvars : Array MVarId := #[]) : MetaM (Expr × Array MVarId) :=
  match type with
  | .forallE _ domain body _ => do
      let argument ← mkFreshExprSyntheticOpaqueMVar domain
      instantiateSourceBinders (body.instantiate1 argument) (mvars.push argument.mvarId!)
  | .mdata _ body =>
      instantiateSourceBinders body mvars
  | result =>
      return (result, mvars)

private def tryCloseGoalWithLocal (goal : MVarId) (locals : Array Expr) : MetaM Bool := do
  let target ← goal.getType'
  for localExpr in locals do
    let saved ← saveState
    if ← isDefEq (← inferType localExpr) target then
      goal.assign localExpr
      return true
    else
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

private def specializesTarget
    (source : Candidate) (targetResult : Expr) (locals : Array Expr) : MetaM Bool := do
  let sourceConst ← mkConstWithFreshMVarLevels source.name
  let sourceType ← inferType sourceConst
  let (sourceResult, sourceMVars) ← instantiateSourceBinders sourceType
  unless ← isDefEq sourceResult targetResult do return false
  closeReplacementSubgoals sourceMVars.toList locals

private def auditTarget
    (target : PreparedCandidate)
    (sources : Array PreparedCandidate)
    (directDependencies : NameMap (Array Name)) :
    MetaM (Array String × Array ReplacementCandidate) :=
  withoutModifyingState do
    withTransparency .reducible do
      let targetConst ← mkConstWithFreshMVarLevels target.candidate.name
      let targetType ← inferType targetConst
      let (locals, _, targetResult) ← forallMetaTelescope targetType
      let baseState ← saveState
      let mut defEq := #[]
      let mut replacements := #[]
      for source in sources do
        baseState.restore
        let sourceDirectDependencies := (directDependencies.find? source.candidate.name).getD #[]
        if sourceDirectDependencies.contains target.candidate.name then
          continue
        let equivalent ←
          if source.binderCount == target.binderCount &&
              sameArgumentHeadSketch source.argumentHeads target.argumentHeads then
            statementDefEq source.candidate target.candidate
          else
            pure false
        if equivalent then
          defEq := defEq.push source.candidate.name.toString
          continue
        if replacements.size >= maxReplacementCandidatesPerTarget then
          continue
        if ← specializesTarget source.candidate targetResult locals then
          replacements := replacements.push {
            name := source.candidate.name.toString
            moduleName := source.candidate.moduleName.toString
          }
      baseState.restore
      return (
        defEq.qsort fun left right => left < right,
        replacements.qsort fun left right => left.name < right.name)

private def collectAuditEntries
    (prepared : Array PreparedCandidate)
    (directDependencies : NameMap (Array Name)) :
    CommandElabM (Array AuditEntry × Nat × Nat) :=
  liftTermElabM do
    let buckets := candidateBuckets prepared
    let mut entries := #[]
    let mut totalProbed := 0
    let mut truncatedTargets := 0
    for target in prepared do
      let bucket := (buckets.get? (coarseFingerprint target)).getD #[]
      let (poolSize, sources) := selectSources bucket target
      let truncated := poolSize > sources.size
      if truncated then truncatedTargets := truncatedTargets + 1
      totalProbed := totalProbed + sources.size
      let (defEq, replacements) ←
        if sources.isEmpty then
          pure (#[], #[])
        else
          liftMetaM <| auditTarget target sources directDependencies
      entries := entries.push {
        target := target.candidate.name.toString
        moduleName := target.candidate.moduleName.toString
        candidatePoolSize := poolSize
        probedCandidateCount := sources.size
        candidatePoolTruncated := truncated
        definitionallyEquivalentTo := defEq
        replacementCandidates := replacements
      }
    return (
      entries.qsort fun left right => left.target < right.target,
      totalProbed,
      truncatedTargets)

private def jsonReplacement (candidate : ReplacementCandidate) : Json :=
  .mkObj [
    ("name", .str candidate.name),
    ("module", .str candidate.moduleName)
  ]

private def jsonEntry (entry : AuditEntry) : Json :=
  .mkObj [
    ("target", .str entry.target),
    ("module", .str entry.moduleName),
    ("candidatePoolSize", .num entry.candidatePoolSize),
    ("probedCandidateCount", .num entry.probedCandidateCount),
    ("candidatePoolTruncated", .bool entry.candidatePoolTruncated),
    ("definitionallyEquivalentTo", .arr <| entry.definitionallyEquivalentTo.map Json.str),
    ("replacementCandidates", .arr <| entry.replacementCandidates.map jsonReplacement)
  ]

private def json (entries : Array AuditEntry) : Json :=
  .arr <| entries.map jsonEntry

private def markdown (entries : Array AuditEntry) : String := Id.run do
  let mut text := "# Theorem replacement audit\n\n"
  text := text ++
    "Candidates are advisory. Each source theorem is specialized with fresh metavariables; its " ++
    "conclusion must be definitionally equal to the target, and every remaining source binder must " ++
    "close from an existing target hypothesis or typeclass synthesis. Search is bounded and may " ++
    "omit valid replacements.\n\n"
  for entry in entries do
    if !entry.definitionallyEquivalentTo.isEmpty || !entry.replacementCandidates.isEmpty then
      text := text ++ s!"## `{entry.target}`\n\n"
      if !entry.definitionallyEquivalentTo.isEmpty then
        text := text ++ "Definitionally equivalent statements:\n\n"
        for candidate in entry.definitionallyEquivalentTo do
          text := text ++ s!"- `{candidate}`\n"
        text := text ++ "\n"
      if !entry.replacementCandidates.isEmpty then
        text := text ++ "Verified replacement candidates:\n\n"
        for candidate in entry.replacementCandidates do
          text := text ++ s!"- `{candidate.name}` ({candidate.moduleName})\n"
        text := text ++ "\n"
  return text

run_cmd do
  let (candidates, projectTheorems) ← collectCandidates
  let prepared := prepareCandidates candidates
  let directDependencies := collectDirectDependencyMap candidates projectTheorems
  let (entries, totalProbed, truncatedTargets) ←
    collectAuditEntries prepared directDependencies
  let defEqTargets := entries.filter fun entry => !entry.definitionallyEquivalentTo.isEmpty
  let replacementTargets := entries.filter fun entry => !entry.replacementCandidates.isEmpty
  let replacementEdges := replacementTargets.foldl (init := 0) fun count entry =>
    count + entry.replacementCandidates.size
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorem-replacements.json") (json entries).pretty
  liftIO <| IO.FS.writeFile (outputDir / "theorem-replacements.md") (markdown entries)
  logInfo m!"Generated theorem replacement audit for {entries.size} declarations; probed {totalProbed} source-target pairs; {truncatedTargets} targets had truncated candidate pools; {defEqTargets.size} targets have definitionally equivalent statements; {replacementTargets.size} targets have verified replacements; {replacementEdges} replacement edges"

end LeanCondensedMatter.TheoremReplacementAudit
