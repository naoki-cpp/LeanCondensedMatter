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
  mathlibProofDependencies : Array String
  mathlibProbedCandidateCount : Nat
  mathlibDiscoveryShapeMatches : Nat
  mathlibDiscoveryProbedCandidateCount : Nat
  mathlibDefinitionallyEquivalentTo : Array String
  mathlibReplacementCandidates : Array ReplacementCandidate

private def maxReplacementCandidatesPerTarget : Nat := 4

/-- Bound the extra proof search for each target; proof dependencies remain unbounded. -/
private def maxMathlibDiscoveryProbesPerTarget : Nat := 8

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.toString.startsWith "LeanCondensedMatter"

private def mathlibModule? (moduleName : Name) : Bool :=
  moduleName.toString.startsWith "Mathlib"

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
    -- Match TheoremCatalog.collectCandidates: theorem-valued structure projections are
    -- assumptions of their structure, not independently proved audit targets.
    if env.isProjectionFn declName then continue
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

private def directMathlibTheoremDependencyNames
    (env : Environment) (declName : Name) (value : Expr) : Array Name :=
  value.foldConsts #[] fun dependency dependencies =>
    if dependency == declName || dependencies.contains dependency then
      dependencies
    else
      match env.find? dependency, declarationModule? env dependency with
      | some (.thmInfo _), some moduleName =>
          if mathlibModule? moduleName then dependencies.push dependency else dependencies
      | _, _ => dependencies

private def theoremCandidate? (env : Environment) (declName : Name) : Option Candidate := do
  let some (.thmInfo theoremInfo) := env.find? declName | none
  let some moduleName := declarationModule? env declName | none
  return { name := declName, moduleName, theoremInfo }

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



/-- Only a coarse, syntactic fingerprint: successful matches are still kernel-checked below.
The full key prioritizes exact result shapes, and the relaxed key permits a different
right-hand side of an equality or equivalence. -/
private def discoveryExactKey (candidate : PreparedCandidate) : String :=
  let head := candidate.resultHead.map Name.toString |>.getD "_"
  let args := candidate.argumentHeads.toList.map fun name? =>
    name?.map Name.toString |>.getD "_"
  s!"{head}:{candidate.resultArity}:{String.intercalate ":" args}"

private def discoveryCoarseKey (candidate : PreparedCandidate) : Option String := do
  let head ← candidate.resultHead
  let first ← candidate.argumentHeads[0]?.getD none
  return s!"{head}:{candidate.resultArity}:{first}"

private structure MathlibDiscoveryIndex where
  exact : Std.HashMap String (Array PreparedCandidate) := {}
  coarse : Std.HashMap String (Array PreparedCandidate) := {}
  indexedCount : Nat := 0

/-- Index all imported Mathlib theorems, not just the theorems named in project proofs.
The index is constructed once, instead of scanning every Mathlib theorem for every target. -/
private def collectMathlibDiscoveryIndex : CommandElabM MathlibDiscoveryIndex := do
  let env ← getEnv
  let mut index : MathlibDiscoveryIndex := {}
  for (name, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    let some moduleName := declarationModule? env name | continue
    unless mathlibModule? moduleName do continue
    if privateDeclarationName? name || extensionTheoremName? name ||
        env.isProjectionFn name then continue
    let candidate := prepareCandidate { name, moduleName, theoremInfo }
    if candidate.resultHead.isNone || !(candidate.argumentHeads.any Option.isSome) then continue
    let exactKey := discoveryExactKey candidate
    let exact := index.exact.insert exactKey
      ((index.exact.getD exactKey #[]).push candidate)
    let coarse := match discoveryCoarseKey candidate with
      | none => index.coarse
      | some key => index.coarse.insert key ((index.coarse.getD key #[]).push candidate)
    index := { exact, coarse, indexedCount := index.indexedCount + 1 }
  return index

private def argumentHeadAgreement (source target : PreparedCandidate) : Nat := Id.run do
  let mut count := 0
  for i in [:min source.argumentHeads.size target.argumentHeads.size] do
    if let some head := source.argumentHeads[i]! then
      if target.argumentHeads[i]! == some head then
        count := count + 1
  return count

private def binderDistance (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

private def discoveryBefore (target source₁ source₂ : PreparedCandidate) : Bool :=
  let agreement₁ := argumentHeadAgreement source₁ target
  let agreement₂ := argumentHeadAgreement source₂ target
  if agreement₁ != agreement₂ then agreement₁ > agreement₂
  else
    let distance₁ := binderDistance source₁.binderCount target.binderCount
    let distance₂ := binderDistance source₂.binderCount target.binderCount
    if distance₁ != distance₂ then distance₁ < distance₂
    else source₁.candidate.name.toString < source₂.candidate.name.toString

/-- Return the bounded, highest-ranked candidate set and the count before truncation.
Direct proof dependencies are excluded here because they are probed separately below. -/
private def discoverMathlibCandidates (index : MathlibDiscoveryIndex)
    (target : PreparedCandidate) (directDependencies : Array Name) :
    Array PreparedCandidate × Nat := Id.run do
  unless target.resultHead.isSome && target.argumentHeads.any Option.isSome do
    return (#[], 0)
  let exactKey := discoveryExactKey target
  let exact := index.exact.getD exactKey #[]
  let coarse := match discoveryCoarseKey target with
    | none => #[]
    | some key => index.coarse.getD key #[]
  let pool := exact ++ coarse.filter (fun candidate => discoveryExactKey candidate != exactKey)
  let matches := pool.filter (fun candidate =>
    !directDependencies.contains candidate.candidate.name)
  let ranked := matches.qsort (discoveryBefore target)
  return ((ranked.toList.take maxMathlibDiscoveryProbesPerTarget).toArray, matches.size)

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

/-- Check whether a source theorem discharges the target by direct specialization.
This is invoked for proof dependencies and for structurally indexed Mathlib discoveries. -/
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
    (prepared : Array PreparedCandidate) (projectTheorems : NameSet)
    (mathlibIndex : MathlibDiscoveryIndex) :
    CommandElabM (Array AuditEntry × Nat × Nat × Nat) := do
  let env ← getEnv
  let byName := candidateMap prepared
  let mut entries := #[]
  let mut totalProjectProbed := 0
  let mut totalMathlibProbed := 0
  let mut totalMathlibDiscoveredProbed := 0
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
    let mathlibDependencyNames := directMathlibTheoremDependencyNames
      env target.candidate.name target.candidate.theoremInfo.value
    let mathlibDependencySources := mathlibDependencyNames.foldl (init := #[]) fun sources dependency =>
      match theoremCandidate? env dependency with
      | none => sources
      | some source =>
          let preparedSource := prepareCandidate source
          if privateDeclarationName? source.name ||
              extensionTheoremName? source.name ||
              !compatibleResultShape preparedSource target then
            sources
          else
            sources.push preparedSource
    let (discovered, shapeMatches) :=
      discoverMathlibCandidates mathlibIndex target mathlibDependencyNames
    let mathlibSources := mathlibDependencySources ++ discovered
    totalProjectProbed := totalProjectProbed + sources.size
    totalMathlibProbed := totalMathlibProbed + mathlibSources.size
    totalMathlibDiscoveredProbed := totalMathlibDiscoveredProbed + discovered.size
    let (defEq, replacements) ←
      if sources.isEmpty then
        pure (#[], #[])
      else
        liftTermElabM <| liftMetaM <| auditTarget target sources
    let (mathlibDefEq, mathlibReplacements) ←
      if mathlibSources.isEmpty then
        pure (#[], #[])
      else
        liftTermElabM <| liftMetaM <| auditTarget target mathlibSources
    entries := entries.push {
      target := target.candidate.name.toString
      moduleName := target.candidate.moduleName.toString
      proofDependencies := (dependencyNames.map Name.toString).qsort fun left right => left < right
      probedCandidateCount := sources.size
      definitionallyEquivalentTo := defEq
      replacementCandidates := replacements
      mathlibProofDependencies :=
        (mathlibDependencyNames.map Name.toString).qsort fun left right => left < right
      mathlibProbedCandidateCount := mathlibSources.size
      mathlibDiscoveryShapeMatches := shapeMatches
      mathlibDiscoveryProbedCandidateCount := discovered.size
      mathlibDefinitionallyEquivalentTo := mathlibDefEq
      mathlibReplacementCandidates := mathlibReplacements
    }
  return (
    entries.qsort fun left right => left.target < right.target,
    totalProjectProbed,
    totalMathlibProbed,
    totalMathlibDiscoveredProbed)

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
    ("replacementCandidates", .arr <| entry.replacementCandidates.map jsonReplacement),
    ("mathlibProofDependencies", .arr <| entry.mathlibProofDependencies.map Json.str),
    ("mathlibProbedCandidateCount", .num entry.mathlibProbedCandidateCount),
    ("mathlibDiscoveryShapeMatches", .num entry.mathlibDiscoveryShapeMatches),
    ("mathlibDiscoveryProbedCandidateCount", .num entry.mathlibDiscoveryProbedCandidateCount),
    ("mathlibDefinitionallyEquivalentTo",
      .arr <| entry.mathlibDefinitionallyEquivalentTo.map Json.str),
    ("mathlibReplacementCandidates",
      .arr <| entry.mathlibReplacementCandidates.map jsonReplacement)
  ]

private def json (entries : Array AuditEntry) : Json :=
  .arr <| entries.map jsonEntry

run_cmd do
  let (candidates, projectTheorems) ← collectCandidates
  let prepared := candidates.map prepareCandidate
  let mathlibIndex ← collectMathlibDiscoveryIndex
  let (entries, totalProjectProbed, totalMathlibProbed, totalMathlibDiscoveredProbed) ←
    collectAuditEntries prepared projectTheorems mathlibIndex
  let defEqTargets := entries.filter fun entry => !entry.definitionallyEquivalentTo.isEmpty
  let replacementTargets := entries.filter fun entry => !entry.replacementCandidates.isEmpty
  let replacementEdges := replacementTargets.foldl (init := 0) fun count entry =>
    count + entry.replacementCandidates.size
  let mathlibDefEqTargets :=
    entries.filter fun entry => !entry.mathlibDefinitionallyEquivalentTo.isEmpty
  let mathlibReplacementTargets :=
    entries.filter fun entry => !entry.mathlibReplacementCandidates.isEmpty
  let mathlibReplacementEdges := mathlibReplacementTargets.foldl (init := 0) fun count entry =>
    count + entry.mathlibReplacementCandidates.size
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorem-replacements.json") (json entries).pretty
  logInfo m!"Generated proof-guided replacement audit for {entries.size} declarations; indexed {mathlibIndex.indexedCount} Mathlib theorems; probed {totalProjectProbed} project proof-dependency pairs and {totalMathlibProbed} Mathlib candidate pairs ({totalMathlibDiscoveredProbed} newly discovered); {defEqTargets.size} targets have definitionally equivalent project proof dependencies; {replacementTargets.size} targets have verified project replacements ({replacementEdges} edges); {mathlibDefEqTargets.size} targets have definitionally equivalent Mathlib proof dependencies; {mathlibReplacementTargets.size} targets have verified Mathlib replacements ({mathlibReplacementEdges} edges)"
end LeanCondensedMatter.TheoremReplacementAudit
