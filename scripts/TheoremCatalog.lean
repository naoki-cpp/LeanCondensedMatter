import Lean
import LeanCondensedMatter
import Lean.Meta.Tactic.Apply
import Lean.Util.CollectAxioms

open Lean Elab Command Meta

namespace LeanCondensedMatter.TheoremCatalog

structure Candidate where
  name : Name
  moduleName : Name
  theoremInfo : TheoremVal

structure ProjectDeclaration where
  name : Name
  moduleName : Name
  type : Expr
  value : Option Expr
  assumptionRoot : Bool

structure PreparedCandidate where
  candidate : Candidate
  binderCount : Nat
  resultHead : Option Name
  resultArity : Nat
  argumentHeads : Array (Option Name)

structure Entry where
  declName : Name
  name : String
  moduleName : String
  statement : String
  docString : Option String
  dependencies : Array String
  declarationDependencies : Array String
  axioms : Array String
  standardAxioms : Array String
  projectAxioms : Array String
  externalAxioms : Array String
  projectAssumptions : Array String
  replacementCandidates : Array String
  definitionallyEquivalentTo : Array String
  directWrapperOf : Option String
  directWrapperTargetModule : Option String
  crossModuleDirectWrapper : Bool

structure CatalogEntry where
  name : String
  moduleName : String
  statement : String
  docString : Option String
  dependencies : Array String
  dependents : Array String
  declarationDependencies : Array String
  declarationConsumers : Array String
  compiledConsumers : Array String
  compiledConsumerCount : Nat
  singleCompiledConsumer : Bool
  terminal : Bool
  axioms : Array String
  standardAxioms : Array String
  projectAxioms : Array String
  externalAxioms : Array String
  projectAssumptions : Array String
  replacementCandidates : Array String
  definitionallyEquivalentTo : Array String
  directWrapperOf : Option String
  directWrapperTargetModule : Option String
  crossModuleDirectWrapper : Bool
  completedMention : Bool
  retainedMention : Bool

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.toString.startsWith "LeanCondensedMatter"

private def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

private def scopedInstanceRegistered? (env : Environment) (declName : Name) : Bool :=
  let state := Meta.instanceExtension.ext.getState env
  let rec visit (components : List Name) (namespaceName : Name) : Bool :=
    match components with
    | [] => false
    | component :: rest =>
        let namespaceName := namespaceName ++ component
        let here :=
          match state.scopedEntries.map.find? namespaceName with
          | none => false
          | some entries => entries.toArray.any fun entry => entry.globalName? == some declName
        here || visit rest namespaceName
  visit declName.getPrefix.components .anonymous

private def localInstanceDeclaration? (env : Environment) (declName : Name) : Bool :=
  if getReducibilityStatusCore env declName != .instanceReducible then
    false
  else
    let globallyRegistered :=
      (Meta.instanceExtension.getState env).instanceNames.find? declName |>.isSome
    !globallyRegistered && !scopedInstanceRegistered? env declName

private def containsSubstring (text pattern : String) : Bool :=
  (text.find? pattern).isSome

private def physicalAssumptionDoc? (docString : Option String) : Bool :=
  match docString with
  | none => false
  | some text =>
      containsSubstring text "postulate.**" ||
      containsSubstring text "Postulate.**" ||
      containsSubstring text "assumption.**" ||
      containsSubstring text "Assumption.**"

private def sourceProjectDeclaration? (env : Environment) (declName : Name) :
    CommandElabM Bool := do
  let some moduleName := declarationModule? env declName | return false
  unless projectModule? moduleName do return false
  if ← liftCoreM <| isAutoDeclOrPrivate_Internal declName then return false
  if localInstanceDeclaration? env declName then return false
  return (← findDeclarationRanges? declName).isSome

private def collectCandidates : CommandElabM (Array Candidate × NameSet) := do
  let env ← getEnv
  let mut candidates := #[]
  let mut theoremNames := NameSet.empty
  for (declName, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    unless ← sourceProjectDeclaration? env declName do continue
    let some moduleName := declarationModule? env declName | continue
    candidates := candidates.push { name := declName, moduleName, theoremInfo }
    theoremNames := theoremNames.insert declName
  return (candidates, theoremNames)

private def collectProjectDeclarations :
    CommandElabM (Array ProjectDeclaration × NameSet × NameSet) := do
  let env ← getEnv
  let mut declarations := #[]
  let mut declarationNames := NameSet.empty
  let mut projectAxioms := NameSet.empty
  for (declName, info) in env.constants.toList do
    unless ← sourceProjectDeclaration? env declName do continue
    let some moduleName := declarationModule? env declName | continue
    let declarationInfo? :=
      match info with
      | .thmInfo theoremInfo => some (theoremInfo.type, some theoremInfo.value, false)
      | .defnInfo definitionInfo => some (definitionInfo.type, some definitionInfo.value, false)
      | .opaqueInfo opaqueInfo => some (opaqueInfo.type, some opaqueInfo.value, false)
      | .axiomInfo axiomInfo => some (axiomInfo.type, none, true)
      | _ => none
    let some (type, value, isAxiom) := declarationInfo? | continue
    let docString ← liftIO <| findDocString? env declName
    let assumptionRoot := isAxiom || physicalAssumptionDoc? docString
    declarations := declarations.push {
      name := declName
      moduleName
      type
      value
      assumptionRoot
    }
    declarationNames := declarationNames.insert declName
    if isAxiom then
      projectAxioms := projectAxioms.insert declName
  return (declarations, declarationNames, projectAxioms)

private def collectProjectConstants
    (projectDeclarations : NameSet) (declName : Name) (expr : Expr)
    (dependencies : Array Name) : Array Name :=
  expr.foldConsts dependencies fun dependency dependencies =>
    if dependency != declName && projectDeclarations.contains dependency &&
        !dependencies.contains dependency then
      dependencies.push dependency
    else
      dependencies

private def directProjectDeclarationDependencyNames
    (projectDeclarations : NameSet) (declaration : ProjectDeclaration) : Array Name :=
  let dependencies :=
    collectProjectConstants projectDeclarations declaration.name declaration.type #[]
  match declaration.value with
  | none => dependencies
  | some value =>
      collectProjectConstants projectDeclarations declaration.name value dependencies

private def directProjectTheoremDependencyNames
    (projectTheorems : NameSet) (declName : Name) (value : Expr) : Array Name :=
  value.foldConsts #[] fun dependency dependencies =>
    if dependency != declName && projectTheorems.contains dependency &&
        !dependencies.contains dependency then
      dependencies.push dependency
    else
      dependencies

private partial def stripDirectWrapperPackaging : Expr → Expr
  | .lam _ _ body _ => stripDirectWrapperPackaging body
  | .mdata _ body => stripDirectWrapperPackaging body
  | value => value

private def privateDeclarationName? (declName : Name) : Bool :=
  declName.toString.startsWith "_private."

private partial def simpleSpecializationArg (projectTheorems : NameSet) : Expr → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .sort _ => true
  | .const name _ => !projectTheorems.contains name
  | .lit _ => true
  | .app fn arg =>
      simpleSpecializationArg projectTheorems fn && simpleSpecializationArg projectTheorems arg
  | .proj _ _ value => simpleSpecializationArg projectTheorems value
  | .mdata _ value => simpleSpecializationArg projectTheorems value
  | _ => false

private def extensionTheoremName? (declName : Name) : Bool :=
  let name := declName.toString
  name.endsWith ".ext" || containsSubstring name ".ext_" || containsSubstring name "_ext_"

private def directWrapperTarget?
    (projectTheorems : NameSet) (declName : Name) (value : Expr) : Option Name := do
  let body := stripDirectWrapperPackaging value
  let wrapped ← body.getAppFn.constName?
  if wrapped == declName || !projectTheorems.contains wrapped || privateDeclarationName? wrapped ||
      extensionTheoremName? wrapped then
    none
  else if body.getAppArgs.all (simpleSpecializationArg projectTheorems) then
    some wrapped
  else
    none

private def sortedNameStrings (names : Array Name) : Array String :=
  (names.map fun name => name.toString).qsort fun left right => left < right

private def sortedNameSetStrings (names : NameSet) : Array String := Id.run do
  let mut result := #[]
  for name in names do
    result := result.push name.toString
  return result.qsort fun left right => left < right

private def addConsumer
    (consumers : NameMap (Array String)) (dependency : Name) (consumer : String) :
    NameMap (Array String) :=
  let existing := (consumers.find? dependency).getD #[]
  let updated := if existing.contains consumer then existing else existing.push consumer
  consumers.insert dependency updated

private def addNameDependency
    (dependencies : NameMap (Array Name)) (declName : Name) (dependency : Name) :
    NameMap (Array Name) :=
  let existing := (dependencies.find? declName).getD #[]
  let updated := if existing.contains dependency then existing else existing.push dependency
  dependencies.insert declName updated

private def collectDeclarationGraph
    (declarations : Array ProjectDeclaration) (projectDeclarations : NameSet) :
    NameMap (Array Name) × NameMap (Array String) := Id.run do
  let mut dependencies : NameMap (Array Name) := {}
  let mut consumers : NameMap (Array String) := {}
  for declaration in declarations do
    let direct := directProjectDeclarationDependencyNames projectDeclarations declaration
    for dependency in direct do
      dependencies := addNameDependency dependencies declaration.name dependency
      consumers := addConsumer consumers dependency declaration.name.toString
  return (dependencies, consumers)

private def projectAssumptionRoots (declarations : Array ProjectDeclaration) : NameSet :=
  declarations.foldl (init := NameSet.empty) fun roots declaration =>
    if declaration.assumptionRoot then roots.insert declaration.name else roots

private def transitiveAssumptionRoots
    (dependencies : NameMap (Array Name)) (roots : NameSet) (start : Name) : Array String := Id.run do
  let initial := (dependencies.find? start).getD #[]
  let rec visit (frontier : Array Name) (visited found : NameSet) : Nat → NameSet
    | 0 => found
    | fuel + 1 =>
        if frontier.isEmpty then
          found
        else
          let (next, visited, found) := frontier.foldl
            (init := (#[], visited, found))
            fun (next, visited, found) name =>
              if visited.contains name then
                (next, visited, found)
              else
                let visited := visited.insert name
                let found := if roots.contains name then found.insert name else found
                let direct := (dependencies.find? name).getD #[]
                let next := direct.foldl (init := next) fun next dependency =>
                  if visited.contains dependency || next.contains dependency then next
                  else next.push dependency
                (next, visited, found)
          visit next visited found fuel
  let found := visit initial NameSet.empty NameSet.empty 10000
  return sortedNameSetStrings found

private def standardAxiom? (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

private def classifyAxioms (axioms : Array Name) (projectAxioms : NameSet) :
    Array String × Array String × Array String × Array String := Id.run do
  let mut standard := #[]
  let mut project := #[]
  let mut external := #[]
  for axiomName in axioms do
    if standardAxiom? axiomName then
      standard := standard.push axiomName
    else if projectAxioms.contains axiomName then
      project := project.push axiomName
    else if axiomName != ``sorryAx then
      external := external.push axiomName
  return (
    sortedNameStrings axioms,
    sortedNameStrings standard,
    sortedNameStrings project,
    sortedNameStrings external)

private def prepareCandidate (candidate : Candidate) : MetaM PreparedCandidate := do
  let theoremConst ← mkConstWithFreshMVarLevels candidate.name
  let theoremType ← inferType theoremConst
  let (binders, _, result) ← forallMetaTelescope theoremType
  let result ← whnf result
  let arguments := result.getAppArgs
  return {
    candidate
    binderCount := binders.size
    resultHead := result.getAppFn.constName?
    resultArity := arguments.size
    argumentHeads := arguments.map fun argument => argument.getAppFn.constName?
  }

private def argumentHeadSketchKey (heads : Array (Option Name)) : String :=
  heads.foldl (init := "") fun key head =>
    let component := head.map (·.toString) |>.getD "_"
    if key.isEmpty then component else key ++ "," ++ component

private def fingerprintKey (candidate : PreparedCandidate) : String :=
  let head := candidate.resultHead.map (·.toString) |>.getD "<none>"
  head ++ "#" ++ toString candidate.resultArity ++ "#" ++
    argumentHeadSketchKey candidate.argumentHeads

private def sameArgumentHeadSketch
    (left right : Array (Option Name)) : Bool := Id.run do
  if left.size != right.size then return false
  for i in [:left.size] do
    if left[i]! != right[i]! then return false
  return true

private def compatibleArgumentHeadSketch
    (left right : Array (Option Name)) : Bool := Id.run do
  if left.size != right.size then return false
  for i in [:left.size] do
    match left[i]!, right[i]! with
    | some leftHead, some rightHead =>
        if leftHead != rightHead then return false
    | _, _ => pure ()
  return true

private def addRelation
    (relations : NameMap (Array String)) (source target : Name) : NameMap (Array String) :=
  addConsumer relations source target.toString

private def candidateBuckets
    (prepared : Array PreparedCandidate) : Std.HashMap String (Array PreparedCandidate) := Id.run do
  let mut buckets : Std.HashMap String (Array PreparedCandidate) := {}
  for candidate in prepared do
    let key := fingerprintKey candidate
    let bucket := (buckets.get? key).getD #[]
    buckets := buckets.insert key (bucket.push candidate)
  return buckets

private def statementDefEq (left right : Candidate) : MetaM Bool :=
  withoutModifyingState do
    withTransparency .reducible do
      let leftConst ← mkConstWithFreshMVarLevels left.name
      let rightConst ← mkConstWithFreshMVarLevels right.name
      isDefEq (← inferType leftConst) (← inferType rightConst)

private def collectDefinitionalEquivalences
    (prepared : Array PreparedCandidate) :
    CommandElabM (NameMap (Array String)) :=
  liftTermElabM do
    let buckets := candidateBuckets prepared
    let mut relations : NameMap (Array String) := {}
    for left in prepared do
      let bucket := (buckets.get? (fingerprintKey left)).getD #[]
      for right in bucket do
        if left.candidate.name.toString < right.candidate.name.toString &&
            left.binderCount == right.binderCount &&
            sameArgumentHeadSketch left.argumentHeads right.argumentHeads &&
            (← liftMetaM <| statementDefEq left.candidate right.candidate) then
          relations := addRelation relations left.candidate.name right.candidate.name
          relations := addRelation relations right.candidate.name left.candidate.name
    return relations

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

private def collectReplacementCandidates
    (prepared : Array PreparedCandidate)
    (definitionallyEquivalent : NameMap (Array String)) :
    CommandElabM (NameMap (Array String)) :=
  liftTermElabM do
    let buckets := candidateBuckets prepared
    let mut replacements : NameMap (Array String) := {}
    for target in prepared do
      let bucket := (buckets.get? (fingerprintKey target)).getD #[]
      let defEqTargets := (definitionallyEquivalent.find? target.candidate.name).getD #[]
      for source in bucket do
        if source.candidate.name != target.candidate.name &&
            !privateDeclarationName? source.candidate.name &&
            !extensionTheoremName? source.candidate.name &&
            !defEqTargets.contains source.candidate.name.toString &&
            compatibleArgumentHeadSketch source.argumentHeads target.argumentHeads &&
            (← liftMetaM <| replacementCloses source.candidate target.candidate) then
          replacements := addRelation replacements target.candidate.name source.candidate.name
    return replacements

private def collectEntries
    (candidates : Array Candidate)
    (projectTheorems projectAxioms : NameSet)
    (declarationDependencies : NameMap (Array Name))
    (assumptionRoots : NameSet)
    (definitionallyEquivalent replacementCandidates : NameMap (Array String)) :
    CommandElabM (Array Entry × NameMap (Array String)) := do
  let env ← getEnv
  let mut entries := #[]
  let mut theoremDependents : NameMap (Array String) := {}
  for candidate in candidates do
    let statement ← liftTermElabM do
      return (← ppExpr candidate.theoremInfo.type).pretty
    let docString ← liftIO <| findDocString? env candidate.name
    let dependencyNames :=
      directProjectTheoremDependencyNames projectTheorems candidate.name candidate.theoremInfo.value
    let directWrapperTarget :=
      directWrapperTarget? projectTheorems candidate.name candidate.theoremInfo.value
    let directWrapperOf := directWrapperTarget.map fun name => name.toString
    let directWrapperTargetModule :=
      directWrapperTarget.bind fun name =>
        (declarationModule? env name).map fun moduleName => moduleName.toString
    let crossModuleDirectWrapper :=
      match directWrapperTargetModule with
      | some targetModule => targetModule != candidate.moduleName.toString
      | none => false
    for dependency in dependencyNames do
      theoremDependents := addConsumer theoremDependents dependency candidate.name.toString
    let collectedAxioms ← Lean.collectAxioms candidate.name
    let (axioms, standardAxioms, projectAxiomsForTheorem, externalAxioms) :=
      classifyAxioms collectedAxioms projectAxioms
    let declarationDependenciesForTheorem :=
      sortedNameStrings ((declarationDependencies.find? candidate.name).getD #[])
    let projectAssumptions :=
      transitiveAssumptionRoots declarationDependencies assumptionRoots candidate.name
    let defEq := ((definitionallyEquivalent.find? candidate.name).getD #[]).qsort (· < ·)
    let replacement :=
      (((replacementCandidates.find? candidate.name).getD #[]).filter fun replacementName =>
        directWrapperOf != some replacementName).qsort (· < ·)
    entries := entries.push {
      declName := candidate.name
      name := candidate.name.toString
      moduleName := candidate.moduleName.toString
      statement
      docString
      dependencies := sortedNameStrings dependencyNames
      declarationDependencies := declarationDependenciesForTheorem
      axioms
      standardAxioms
      projectAxioms := projectAxiomsForTheorem
      externalAxioms
      projectAssumptions
      replacementCandidates := replacement
      definitionallyEquivalentTo := defEq
      directWrapperOf
      directWrapperTargetModule
      crossModuleDirectWrapper
    }
  return (
    entries.qsort fun left right => left.name < right.name,
    theoremDependents)

private def collectCompiledConsumers
    (projectTheorems : NameSet) : CommandElabM (NameMap (Array String)) := do
  let env ← getEnv
  let mut consumers : NameMap (Array String) := {}
  for (declName, info) in env.constants.toList do
    unless ← sourceProjectDeclaration? env declName do continue
    let value? :=
      match info with
      | .thmInfo theoremInfo => some theoremInfo.value
      | .defnInfo definitionInfo => some definitionInfo.value
      | .opaqueInfo opaqueInfo => some opaqueInfo.value
      | _ => none
    let some value := value? | continue
    let dependencyNames := directProjectTheoremDependencyNames projectTheorems declName value
    for dependency in dependencyNames do
      consumers := addConsumer consumers dependency declName.toString
  return consumers

private def declarationBaseName (declName : String) : String :=
  (declName.splitOn ".").getLastD declName

private def mentionedInCompleted (completed declName : String) : Bool :=
  containsSubstring completed declName ||
    containsSubstring completed s!"`{declarationBaseName declName}`"

private def mentionedInRetained (retained declName : String) : Bool :=
  containsSubstring retained s!"- `{declName}`"

private def sortedConsumers
    (consumers : NameMap (Array String)) (declName : Name) : Array String :=
  ((consumers.find? declName).getD #[]).qsort fun left right => left < right

private def annotateEntries
    (entries : Array Entry)
    (theoremDependents declarationConsumers compiledConsumers : NameMap (Array String))
    (completed retained : String) : Array CatalogEntry :=
  entries.map fun entry =>
    let dependents := sortedConsumers theoremDependents entry.declName
    let declarationConsumers := sortedConsumers declarationConsumers entry.declName
    let compiledConsumers := sortedConsumers compiledConsumers entry.declName
    let compiledConsumerCount := compiledConsumers.size
    let singleCompiledConsumer := compiledConsumerCount == 1
    let terminal := dependents.isEmpty
    {
      name := entry.name
      moduleName := entry.moduleName
      statement := entry.statement
      docString := entry.docString
      dependencies := entry.dependencies
      dependents
      declarationDependencies := entry.declarationDependencies
      declarationConsumers
      compiledConsumers
      compiledConsumerCount
      singleCompiledConsumer
      terminal
      axioms := entry.axioms
      standardAxioms := entry.standardAxioms
      projectAxioms := entry.projectAxioms
      externalAxioms := entry.externalAxioms
      projectAssumptions := entry.projectAssumptions
      replacementCandidates := entry.replacementCandidates
      definitionallyEquivalentTo := entry.definitionallyEquivalentTo
      directWrapperOf := entry.directWrapperOf
      directWrapperTargetModule := entry.directWrapperTargetModule
      crossModuleDirectWrapper := entry.crossModuleDirectWrapper
      completedMention := terminal && mentionedInCompleted completed entry.name
      retainedMention := mentionedInRetained retained entry.name
    }

private def dependencyEdgeCount (entries : Array CatalogEntry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.dependencies.size

private def declarationDependencyEdgeCount (entries : Array CatalogEntry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.declarationDependencies.size

private def replacementEdgeCount (entries : Array CatalogEntry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.replacementCandidates.size

private def definitionalEquivalencePairCount (entries : Array CatalogEntry) : Nat :=
  (entries.foldl (init := 0) fun count entry => count + entry.definitionallyEquivalentTo.size) / 2

private def terminalEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.terminal

private def compiledConsumerFreeEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.compiledConsumers.isEmpty

private def singleCompiledConsumerEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.singleCompiledConsumer

private def directWrapperEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.directWrapperOf.isSome

private def soleCompiledConsumer? (entry : CatalogEntry) : Option String :=
  match entry.compiledConsumers.toList with
  | [consumer] => some consumer
  | _ => none

private def catalogEntry? (entries : Array CatalogEntry) (name : String) : Option CatalogEntry :=
  let rec search (lower upper : Nat) : Nat → Option CatalogEntry
    | 0 => none
    | fuel + 1 =>
        if lower < upper then
          let middle := (lower + upper) / 2
          if hmiddle : middle < entries.size then
            let entry := entries[middle]
            if entry.name == name then
              some entry
            else if entry.name < name then
              search (middle + 1) upper fuel
            else
              search lower middle fuel
          else
            none
        else
          none
  search 0 entries.size entries.size

private def sortedStringContains (names : Array String) (target : String) : Bool :=
  let rec search (lower upper : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
        if lower < upper then
          let middle := (lower + upper) / 2
          if hmiddle : middle < names.size then
            let current := names[middle]
            if current == target then
              true
            else if current < target then
              search (middle + 1) upper fuel
            else
              search lower middle fuel
          else
            false
        else
          false
  search 0 names.size names.size

private def singleConsumerTheoremTargets (entries : Array CatalogEntry) : Array String :=
  let targets := entries.foldl (init := (#[] : Array String)) fun targets entry =>
    match soleCompiledConsumer? entry with
    | some consumer =>
        if entry.dependents.contains consumer then targets.push consumer else targets
    | none => targets
  targets.qsort fun left right => left < right

private def followSingleConsumerChain
    (entries : Array CatalogEntry) (start : String) : Array String :=
  let rec loop (current : String) (chain : Array String) : Nat → Array String
    | 0 => chain
    | fuel + 1 =>
        match catalogEntry? entries current with
        | none => chain
        | some entry =>
            match soleCompiledConsumer? entry with
            | none => chain
            | some consumer =>
                if chain.contains consumer then
                  chain
                else
                  let nextChain := chain.push consumer
                  match catalogEntry? entries consumer with
                  | none => nextChain
                  | some _ => loop consumer nextChain fuel
  loop start #[start] entries.size

private def singleConsumerChainForEntry
    (entries : Array CatalogEntry) (singleConsumerTheoremTargets : Array String)
    (entry : CatalogEntry) : Array String :=
  match soleCompiledConsumer? entry with
  | none => #[]
  | some _ =>
      if sortedStringContains singleConsumerTheoremTargets entry.name then
        #[]
      else
        let chain := followSingleConsumerChain entries entry.name
        if chain.size > 2 then chain else #[]

private def singleConsumerChains (entries : Array CatalogEntry) : Array (Array String) :=
  let predecessorTargets := singleConsumerTheoremTargets entries
  entries.foldl (init := (#[] : Array (Array String))) fun chains entry =>
    let chain := singleConsumerChainForEntry entries predecessorTargets entry
    if chain.isEmpty then chains else chains.push chain

private def chainText (chain : Array String) : String :=
  chain.foldl (init := "") fun text name =>
    if text == "" then s!"`{name}`" else text ++ s!" → `{name}`"

private def markdown (entries : Array CatalogEntry) (chains : Array (Array String)) : String := Id.run do
  let retainedEntries := entries.filter fun entry => entry.retainedMention
  let terminals := terminalEntries entries
  let completedTerminals := terminals.filter fun entry => entry.completedMention
  let retainedTerminals := terminals.filter fun entry => entry.retainedMention
  let reviewQueue :=
    terminals.filter fun entry => !entry.completedMention && !entry.retainedMention
  let priorityReviewQueue := compiledConsumerFreeEntries reviewQueue
  let singleConsumerEntries := singleCompiledConsumerEntries entries
  let retainedSingleConsumers :=
    singleConsumerEntries.filter fun entry => entry.retainedMention
  let singleConsumerReviewQueue :=
    singleConsumerEntries.filter fun entry => !entry.retainedMention
  let directWrappers := directWrapperEntries entries
  let retainedDirectWrappers :=
    directWrappers.filter fun entry => entry.retainedMention
  let directWrapperReviewQueue :=
    directWrappers.filter fun entry => !entry.retainedMention
  let crossModuleDirectWrappers :=
    directWrappers.filter fun entry => entry.crossModuleDirectWrapper
  let crossModuleDirectWrapperReviewQueue :=
    directWrapperReviewQueue.filter fun entry => entry.crossModuleDirectWrapper
  let terminalsWithCompiledConsumers :=
    terminals.filter fun entry => !entry.compiledConsumers.isEmpty
  let replacementEntries := entries.filter fun entry => !entry.replacementCandidates.isEmpty
  let replacementReviewQueue := replacementEntries.filter fun entry => !entry.retainedMention
  let defEqEntries := entries.filter fun entry => !entry.definitionallyEquivalentTo.isEmpty
  let defEqReviewQueue := defEqEntries.filter fun entry => !entry.retainedMention
  let assumptionEntries := entries.filter fun entry => !entry.projectAssumptions.isEmpty
  let mut output := "# LeanCondensedMatter theorem catalog\n\n"
  output := output ++ "This file is generated from source-declared theorems in LeanCondensedMatter modules. Do not edit it manually.\n\n"
  output := output ++ "The JSON catalog combines proof-term dependency data with advisory semantic audit metadata. Exact duplicate rejection and sorry rejection remain separate hard CI checks; replacement candidates, definitional equivalence, declaration-level dependency data, and assumption provenance are advisory.\n\n"
  output := output ++ s!"Theorems: {entries.size}\n\n"
  output := output ++ s!"Dependency edges: {dependencyEdgeCount entries}\n\n"
  output := output ++ s!"Declaration dependency edges from theorem nodes: {declarationDependencyEdgeCount entries}\n\n"
  output := output ++ s!"Retained audit declarations: {retainedEntries.size}\n\n"
  output := output ++ s!"Terminal theorems: {terminals.size}\n\n"
  output := output ++ s!"Terminal theorems mentioned in completed.md: {completedTerminals.size}\n\n"
  output := output ++ s!"Terminal theorems documented as retained: {retainedTerminals.size}\n\n"
  output := output ++ s!"Terminal theorems with compiled project consumers: {terminalsWithCompiledConsumers.size}\n\n"
  output := output ++ s!"Terminal theorem review queue: {reviewQueue.size}\n\n"
  output := output ++ s!"Priority terminal review queue with no compiled project consumers: {priorityReviewQueue.size}\n\n"
  output := output ++ s!"Single-consumer theorems documented as retained: {retainedSingleConsumers.size}\n\n"
  output := output ++ s!"Single-consumer theorem review queue: {singleConsumerReviewQueue.size}\n\n"
  output := output ++ s!"Direct-wrapper candidates: {directWrappers.size}\n\n"
  output := output ++ s!"Direct-wrapper candidates documented as retained: {retainedDirectWrappers.size}\n\n"
  output := output ++ s!"Direct-wrapper review queue: {directWrapperReviewQueue.size}\n\n"
  output := output ++ s!"Cross-module direct-wrapper candidates: {crossModuleDirectWrappers.size}\n\n"
  output := output ++ s!"Cross-module direct-wrapper review queue: {crossModuleDirectWrapperReviewQueue.size}\n\n"
  output := output ++ s!"Multi-step single-consumer chains: {chains.size}\n\n"
  output := output ++ s!"Theorems with replacement candidates: {replacementEntries.size}\n\n"
  output := output ++ s!"Replacement candidate edges: {replacementEdgeCount entries}\n\n"
  output := output ++ s!"Definitional-equivalence pairs: {definitionalEquivalencePairCount entries}\n\n"
  output := output ++ s!"Theorems with project assumptions: {assumptionEntries.size}\n\n"
  output := output ++ "`replacementCandidates` records existing project theorems that Lean can conservatively apply to the target theorem conclusion under the target binders, with remaining application goals discharged only by target-local hypotheses or typeclass synthesis. Candidates are bucketed by result-head, result-arity, and result-argument-head fingerprints before Meta-level application, and direct-wrapper and definitionally-equivalent relations are reported separately. No `simp` or general proof search is used.\n\n"
  output := output ++ "`definitionallyEquivalentTo` is weaker than the hard exact-duplicate check: it is computed by Meta-level definitional equality under reducible transparency after cheap fingerprinting. Exact structural duplicates remain the responsibility of `CheckDuplicates.lean` and are not weakened by this advisory relation.\n\n"
  output := output ++ "`axioms` records kernel axiom provenance from `Lean.collectAxioms`. `standardAxioms` classifies `propext`, `Classical.choice`, and `Quot.sound`; `projectAxioms` records source-declared LeanCondensedMatter axioms; `externalAxioms` records other non-`sorryAx` axioms. `projectAssumptions` is a separate model-level provenance relation: it follows compiled declaration dependencies transitively to source declarations explicitly documented as a postulate/assumption or declared as a project axiom. Modeling assumptions represented only as theorem hypotheses remain visible in the theorem statement and are not promoted to global assumption roots.\n\n"
  output := output ++ "`declarationDependencies` and `declarationConsumers` generalize the graph beyond theorem proof dependencies by scanning both declaration types and values for source-declared project theorem/definition/opaque/axiom references. The legacy `dependencies`, `dependents`, and `compiledConsumers` fields retain their narrower semantics for compatibility with existing review queues and the graph explorer.\n\n"
  output := output ++ "## Replacement-candidate review queue\n\n"
  for entry in replacementReviewQueue do
    for replacement in entry.replacementCandidates do
      output := output ++ s!"- `{entry.name}` ⇐ `{replacement}` — module `{entry.moduleName}`; compiled consumers: {entry.compiledConsumerCount}; direct wrapper: {entry.directWrapperOf.isSome}\n"
  output := output ++ "\n## Definitionally equivalent statement review queue\n\n"
  for entry in defEqReviewQueue do
    for equivalent in entry.definitionallyEquivalentTo do
      if entry.name < equivalent then
        output := output ++ s!"- `{entry.name}` ≃ `{equivalent}` — reducible definitional equality; exact duplicate detection remains separate\n"
  output := output ++ "\n## Project-assumption provenance\n\n"
  for entry in assumptionEntries do
    output := output ++ s!"- `{entry.name}` — {entry.projectAssumptions.size} assumption root(s): "
    output := entry.projectAssumptions.foldl (init := output) fun output assumption =>
      output ++ s!"`{assumption}` "
    output := output ++ "\n"
  output := output ++ "\n## Direct-wrapper review queue\n\n"
  for entry in directWrapperReviewQueue do
    let target := entry.directWrapperOf.getD "<unknown>"
    let targetModule := entry.directWrapperTargetModule.getD "<unknown>"
    output := output ++ s!"- `{entry.name}` → `{target}` — module `{entry.moduleName}`; target module: `{targetModule}`; compiled consumers: {entry.compiledConsumerCount}; single consumer: {entry.singleCompiledConsumer}; terminal: {entry.terminal}; cross-module: {entry.crossModuleDirectWrapper}\n"
  output := output ++ "\n## Multi-step single-consumer chains\n\n"
  for chain in chains do
    output := output ++ s!"- {chainText chain}\n"
  output := output ++ "\n## Single-consumer theorem review queue\n\n"
  for entry in singleConsumerReviewQueue do
    for consumer in entry.compiledConsumers do
      output := output ++ s!"- `{entry.name}` → `{consumer}` — module `{entry.moduleName}`; theorem dependents: {entry.dependents.size}; direct prerequisites: {entry.dependencies.size}; direct wrapper: {entry.directWrapperOf.isSome}\n"
  output := output ++ "\n## Priority terminal theorem review queue\n\n"
  for entry in priorityReviewQueue do
    output := output ++ s!"- `{entry.name}` — module `{entry.moduleName}`; direct prerequisites: {entry.dependencies.size}; direct wrapper: {entry.directWrapperOf.isSome}\n"
  output := output ++ "\n## Full terminal theorem review queue\n\n"
  for entry in reviewQueue do
    output := output ++ s!"- `{entry.name}` — module `{entry.moduleName}`; direct prerequisites: {entry.dependencies.size}; compiled consumers: {entry.compiledConsumerCount}; direct wrapper: {entry.directWrapperOf.isSome}\n"
  output := output ++ "\n"
  for entry in entries do
    output := output ++ s!"## `{entry.name}`\n\n"
    output := output ++ s!"Module: `{entry.moduleName}`\n\n"
    output := output ++ s!"```lean\n{entry.statement}\n```\n\n"
    if let some docString := entry.docString then
      output := output ++ docString.trimAscii.toString ++ "\n\n"
  return output

private def json (entries : Array CatalogEntry) : Json :=
  .arr <| entries.map fun entry =>
    .mkObj [
      ("name", .str entry.name),
      ("module", .str entry.moduleName),
      ("statement", .str entry.statement),
      ("docString", entry.docString.map Json.str |>.getD .null),
      ("dependencies", .arr <| entry.dependencies.map Json.str),
      ("dependents", .arr <| entry.dependents.map Json.str),
      ("declarationDependencies", .arr <| entry.declarationDependencies.map Json.str),
      ("declarationConsumers", .arr <| entry.declarationConsumers.map Json.str),
      ("compiledConsumers", .arr <| entry.compiledConsumers.map Json.str),
      ("compiledConsumerCount", .num entry.compiledConsumerCount),
      ("singleCompiledConsumer", .bool entry.singleCompiledConsumer),
      ("terminal", .bool entry.terminal),
      ("axioms", .arr <| entry.axioms.map Json.str),
      ("standardAxioms", .arr <| entry.standardAxioms.map Json.str),
      ("projectAxioms", .arr <| entry.projectAxioms.map Json.str),
      ("externalAxioms", .arr <| entry.externalAxioms.map Json.str),
      ("projectAssumptions", .arr <| entry.projectAssumptions.map Json.str),
      ("replacementCandidates", .arr <| entry.replacementCandidates.map Json.str),
      ("definitionallyEquivalentTo", .arr <| entry.definitionallyEquivalentTo.map Json.str),
      ("directWrapperOf", entry.directWrapperOf.map Json.str |>.getD .null),
      ("directWrapperTargetModule", entry.directWrapperTargetModule.map Json.str |>.getD .null),
      ("crossModuleDirectWrapper", .bool entry.crossModuleDirectWrapper),
      ("completedMention", .bool entry.completedMention),
      ("retainedMention", .bool entry.retainedMention)
    ]

run_cmd do
  let (candidates, projectTheorems) ← collectCandidates
  let (declarations, projectDeclarations, projectAxioms) ← collectProjectDeclarations
  let (declarationDependencies, declarationConsumers) :=
    collectDeclarationGraph declarations projectDeclarations
  let assumptionRoots := projectAssumptionRoots declarations
  let prepared ← liftTermElabM do
    liftMetaM <| candidates.mapM prepareCandidate
  let definitionallyEquivalent ← collectDefinitionalEquivalences prepared
  let replacementCandidates ←
    collectReplacementCandidates prepared definitionallyEquivalent
  let (entries, theoremDependents) ←
    collectEntries candidates projectTheorems projectAxioms declarationDependencies assumptionRoots
      definitionallyEquivalent replacementCandidates
  let compiledConsumers ← collectCompiledConsumers projectTheorems
  let completed ← liftIO <| IO.FS.readFile ("notes" / "completed.md")
  let retained ← liftIO <| IO.FS.readFile ("notes" / "theorem-catalog-retained.md")
  let catalog :=
    annotateEntries entries theoremDependents declarationConsumers compiledConsumers completed retained
  let chains := singleConsumerChains catalog
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorems.md") (markdown catalog chains)
  liftIO <| IO.FS.writeFile (outputDir / "theorems.json") (json catalog).pretty
  logInfo m!"Generated theorem catalog with {catalog.size} theorem nodes, {dependencyEdgeCount catalog} theorem dependency edges, {declarationDependencyEdgeCount catalog} declaration dependency edges from theorem nodes, {replacementEdgeCount catalog} replacement-candidate edges, and {definitionalEquivalencePairCount catalog} definitional-equivalence pairs."

end LeanCondensedMatter.TheoremCatalog