import Lean
import LeanCondensedMatter
import Lean.Util.CollectAxioms

open Lean Elab Command Meta

namespace LeanCondensedMatter.TheoremCatalog

structure Candidate where
  name : Name
  moduleName : Name
  theoremInfo : TheoremVal

structure Entry where
  declName : Name
  name : String
  moduleName : String
  statement : String
  docString : Option String
  dependencies : Array String
  axioms : Array String
  standardAxioms : Array String
  projectAxioms : Array String
  externalAxioms : Array String
  simpLemma : Bool
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
  compiledConsumers : Array String
  compiledConsumerCount : Nat
  singleCompiledConsumer : Bool
  soleCompiledConsumerPrivate : Bool
  simpLemma : Bool
  terminal : Bool
  axioms : Array String
  standardAxioms : Array String
  projectAxioms : Array String
  externalAxioms : Array String
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

private def collectCandidates : CommandElabM (Array Candidate × NameSet) := do
  let env ← getEnv
  let mut candidates := #[]
  let mut theoremNames := NameSet.empty
  for (declName, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    -- Generated declarations such as structure extensionality and injectivity
    -- theorems do not have their own source declaration range.
    unless (← findDeclarationRanges? declName).isSome do continue
    candidates := candidates.push { name := declName, moduleName, theoremInfo }
    theoremNames := theoremNames.insert declName
  return (candidates, theoremNames)

private def collectProjectAxioms : CommandElabM NameSet := do
  let env ← getEnv
  let mut projectAxioms := NameSet.empty
  for (declName, info) in env.constants.toList do
    let .axiomInfo _ := info | continue
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    unless (← findDeclarationRanges? declName).isSome do continue
    projectAxioms := projectAxioms.insert declName
  return projectAxioms

private def directProjectTheoremDependencyNames
    (projectTheorems : NameSet) (declName : Name) (value : Expr) : Array Name :=
  value.foldConsts #[] fun dependency dependencies =>
    if dependency != declName && projectTheorems.contains dependency &&
        !dependencies.contains dependency then
      dependencies.push dependency
    else
      dependencies

/-- Remove only packaging that preserves the direct-application shape. `let` bindings are not
substituted: a theorem that constructs proof terms internally should not be classified as a thin
specialization. -/
private partial def stripDirectWrapperPackaging : Expr → Expr
  | .lam _ _ body _ => stripDirectWrapperPackaging body
  | .mdata _ body => stripDirectWrapperPackaging body
  | value => value

private def privateDeclarationName? (declName : Name) : Bool :=
  declName.toString.startsWith "_private."

private def privateDeclarationString? (declName : String) : Bool :=
  declName.startsWith "_private."

private def simpLemma? (simpTheorems : SimpTheorems) (declName : Name) : Bool :=
  simpTheorems.isLemma (.decl declName true false) ||
    simpTheorems.isLemma (.decl declName true true) ||
    simpTheorems.isLemma (.decl declName false false) ||
    simpTheorems.isLemma (.decl declName false true)

/-- Restrict direct-wrapper candidates to applications assembled from variables, non-theorem
constants, projections, and other simple specialization arguments. A project theorem occurring in
an argument is evidence of substantive proof construction rather than bare specialization. -/
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

private def containsSubstring (text pattern : String) : Bool :=
  (text.find? pattern).isSome

/-- Extensionality lemmas are proof mechanisms, not evidence that the result is merely a
specialization of the extensionality theorem. -/
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

private def addConsumer
    (consumers : NameMap (Array String)) (dependency : Name) (consumer : String) :
    NameMap (Array String) :=
  let existing := (consumers.find? dependency).getD #[]
  let updated := if existing.contains consumer then existing else existing.push consumer
  consumers.insert dependency updated

private def collectEntries
    (projectAxioms : NameSet) :
    CommandElabM (Array Entry × NameSet × NameMap (Array String)) := do
  let env ← getEnv
  let simpTheorems := simpExtension.getState env
  let (candidates, projectTheorems) ← collectCandidates
  let mut entries := #[]
  let mut theoremDependents : NameMap (Array String) := {}
  for candidate in candidates do
    let statement ← liftTermElabM do
      return (← ppExpr candidate.theoremInfo.type).pretty
    let docString ← liftIO <| findDocString? env candidate.name
    let dependencyNames := directProjectTheoremDependencyNames
      projectTheorems candidate.name candidate.theoremInfo.value
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
    entries := entries.push {
      declName := candidate.name
      name := candidate.name.toString
      moduleName := candidate.moduleName.toString
      statement
      docString
      dependencies := sortedNameStrings dependencyNames
      axioms
      standardAxioms
      projectAxioms := projectAxiomsForTheorem
      externalAxioms
      simpLemma := simpLemma? simpTheorems candidate.name
      directWrapperOf
      directWrapperTargetModule
      crossModuleDirectWrapper
    }
  return (
    entries.qsort fun left right => left.name < right.name,
    projectTheorems,
    theoremDependents)

private def collectCompiledConsumers
    (projectTheorems : NameSet) : CommandElabM (NameMap (Array String)) := do
  let env ← getEnv
  let mut consumers : NameMap (Array String) := {}
  for (declName, info) in env.constants.toList do
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    unless (← findDeclarationRanges? declName).isSome do continue
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
    (theoremDependents compiledConsumers : NameMap (Array String))
    (completed retained : String) : Array CatalogEntry :=
  entries.map fun entry =>
    let dependents := sortedConsumers theoremDependents entry.declName
    let compiledConsumers := sortedConsumers compiledConsumers entry.declName
    let compiledConsumerCount := compiledConsumers.size
    let singleCompiledConsumer := compiledConsumerCount == 1
    let soleCompiledConsumerPrivate :=
      match compiledConsumers.toList with
      | [consumer] => privateDeclarationString? consumer
      | _ => false
    let terminal := dependents.isEmpty
    {
      name := entry.name
      moduleName := entry.moduleName
      statement := entry.statement
      docString := entry.docString
      dependencies := entry.dependencies
      dependents
      compiledConsumers
      compiledConsumerCount
      singleCompiledConsumer
      soleCompiledConsumerPrivate
      simpLemma := entry.simpLemma
      terminal
      axioms := entry.axioms
      standardAxioms := entry.standardAxioms
      projectAxioms := entry.projectAxioms
      externalAxioms := entry.externalAxioms
      directWrapperOf := entry.directWrapperOf
      directWrapperTargetModule := entry.directWrapperTargetModule
      crossModuleDirectWrapper := entry.crossModuleDirectWrapper
      completedMention := terminal && mentionedInCompleted completed entry.name
      retainedMention := mentionedInRetained retained entry.name
    }

private def dependencyEdgeCount (entries : Array CatalogEntry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.dependencies.size

private def terminalEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.terminal

private def compiledConsumerFreeEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.compiledConsumers.isEmpty

private def singleCompiledConsumerEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.singleCompiledConsumer

private def privateSingleConsumerReviewEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry =>
    !entry.retainedMention && !entry.simpLemma && !privateDeclarationString? entry.name &&
      entry.soleCompiledConsumerPrivate

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
  let privateSingleConsumerReviewQueue := privateSingleConsumerReviewEntries entries
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
  let projectAxiomEntries := entries.filter fun entry => !entry.projectAxioms.isEmpty
  let externalAxiomEntries := entries.filter fun entry => !entry.externalAxioms.isEmpty
  let mut output := "# LeanCondensedMatter theorem catalog\n\n"
  output := output ++ "This file is generated from source-declared theorems in LeanCondensedMatter modules. Do not edit it manually.\n\n"
  output := output ++ "The JSON catalog records theorem attributes on one entry per declaration: direct theorem dependencies/dependents, compiled project-declaration consumers, kernel axiom provenance, simp status, terminal status, retained/completed annotations, and conservative direct-wrapper metadata. Dependencies and consumers are distinct declaration-level graph edges: repeated references from one compiled declaration are counted once. Compiled consumers scan source-declared project theorem, definition, and opaque-declaration values.\n\n"
  output := output ++ s!"Theorems: {entries.size}\n\n"
  output := output ++ s!"Dependency edges: {dependencyEdgeCount entries}\n\n"
  output := output ++ s!"Retained audit declarations: {retainedEntries.size}\n\n"
  output := output ++ s!"Terminal theorems: {terminals.size}\n\n"
  output := output ++ s!"Terminal theorems mentioned in completed.md: {completedTerminals.size}\n\n"
  output := output ++ s!"Terminal theorems documented as retained: {retainedTerminals.size}\n\n"
  output := output ++ s!"Terminal theorems with compiled project consumers: {terminalsWithCompiledConsumers.size}\n\n"
  output := output ++ s!"Terminal theorem review queue: {reviewQueue.size}\n\n"
  output := output ++ s!"Priority terminal review queue with no compiled project consumers: {priorityReviewQueue.size}\n\n"
  output := output ++ s!"Single-consumer theorems documented as retained: {retainedSingleConsumers.size}\n\n"
  output := output ++ s!"Single-consumer theorem review queue: {singleConsumerReviewQueue.size}\n\n"
  output := output ++ s!"Priority public non-simp theorems with a sole private compiled consumer: {privateSingleConsumerReviewQueue.size}\n\n"
  output := output ++ s!"Direct-wrapper candidates: {directWrappers.size}\n\n"
  output := output ++ s!"Direct-wrapper candidates documented as retained: {retainedDirectWrappers.size}\n\n"
  output := output ++ s!"Direct-wrapper review queue: {directWrapperReviewQueue.size}\n\n"
  output := output ++ s!"Cross-module direct-wrapper candidates: {crossModuleDirectWrappers.size}\n\n"
  output := output ++ s!"Cross-module direct-wrapper review queue: {crossModuleDirectWrapperReviewQueue.size}\n\n"
  output := output ++ s!"Multi-step single-consumer chains: {chains.size}\n\n"
  output := output ++ s!"Theorems depending on project axioms: {projectAxiomEntries.size}\n\n"
  output := output ++ s!"Theorems depending on external nonstandard axioms: {externalAxiomEntries.size}\n\n"
  output := output ++ "Here a terminal theorem means a theorem with no direct project-theorem dependents: no other source-declared project theorem in the catalog retains it in its compiled proof term. This is the endpoint side of the theorem proof graph, not the prerequisite-free side.\n\n"
  output := output ++ "`compiledConsumers` is broader: it records source-declared project theorems, definitions, and opaque declarations whose compiled values retain a reference to the theorem. `compiledConsumerCount` and `singleCompiledConsumer` are derived from that same array, so usage status is an attribute of the theorem rather than a separately maintained candidate set. `soleCompiledConsumerPrivate` additionally records whether the unique compiled consumer, when one exists, is a private declaration. It is still not a source-level use analysis: simplification, unfolding, and definitional reduction can erase an explicit source reference before compilation. Therefore a theorem with no compiled consumer is only a higher-priority review candidate, never automatic evidence that the theorem is unused.\n\n"
  output := output ++ "`axioms` records transitive kernel axiom dependencies from `Lean.collectAxioms`. `standardAxioms` classifies `propext`, `Classical.choice`, and `Quot.sound`; `projectAxioms` records source-declared LeanCondensedMatter axioms; `externalAxioms` records other non-`sorryAx` axioms. This is kernel provenance, not a replacement for explicit model assumptions represented as theorem hypotheses.\n\n"
  output := output ++ "`simpLemma` records membership in Lean's active default simp extension, including simp attributes applied separately from the theorem declaration. The priority private-consumer queue excludes simp lemmas because public canonical evaluation/normalization rules can remain useful API even when their only currently retained compiled consumer is private. This exclusion is a ranking heuristic, not a claim that every simp theorem should be retained.\n\n"
  output := output ++ "`directWrapperOf` is a conservative proof-term attribute: after removing only lambda/metadata packaging, the theorem body must be a direct application of another non-private source-declared project theorem and all application arguments must have a simple specialization shape without references to other project theorems. Extensionality lemmas are excluded because they are commonly proof mechanisms for genuinely new results. `directWrapperTargetModule` and `crossModuleDirectWrapper` record where that target lives. These attributes are advisory and do not imply that a domain-specific specialization lacks independent API value.\n\n"
  output := output ++ "`retainedMention` records a semantic review disposition from `notes/theorem-catalog-retained.md`. Retained declarations keep all structural attributes in the full catalog, but are omitted from terminal, single-consumer, private-consumer, and direct-wrapper review queues so the queues contain unresolved audit work rather than repeatedly surfacing reviewed API.\n\n"
  output := output ++ "A single-consumer theorem has exactly one distinct compiled project-declaration consumer. Multi-step chains follow that unique edge through theorem consumers until the chain reaches a theorem without exactly one compiled consumer, or a non-theorem definition/opaque endpoint. Only chains with at least two single-consumer edges are listed separately. These highlight public wrappers and proof-routing stages that may be candidates for inlining, privatization, or deletion; source search and semantic review remain required before changing the API. Retained declarations can still appear in these chains because the chains describe graph structure rather than review status.\n\n"
  output := output ++ "A mention in `notes/completed.md` is evidence that a terminal endpoint is an intentional completed result. A mention in `notes/theorem-catalog-retained.md` is evidence that a declaration surfaced by one or more audit signals was semantically reviewed and intentionally retained. Terminal declarations with neither disposition remain review candidates: compare their statement and module with `notes/roadmap.md` and the detailed roadmaps to decide whether they are roadmap intermediates that still need a consumer, intentional local endpoints, or unnecessary public theorems.\n\n"
  output := output ++ "## Project axiom provenance\n\n"
  output := output ++ "Each row lists the source-declared LeanCondensedMatter axioms transitively used by a theorem. Standard logical axioms remain available in the JSON entry but are omitted here.\n\n"
  for entry in projectAxiomEntries do
    output := output ++ s!"- `{entry.name}` — "
    output := entry.projectAxioms.foldl (init := output) fun output axiomName =>
      output ++ s!"`{axiomName}` "
    output := output ++ "\n"
  output := output ++ "\n## Direct-wrapper review queue\n\n"
  output := output ++ "Each row is an unresolved direct-wrapper candidate with its relevant audit attributes shown together. Declarations recorded in `notes/theorem-catalog-retained.md` remain in the full catalog but are omitted from this queue.\n\n"
  for entry in directWrapperReviewQueue do
    let target := entry.directWrapperOf.getD "<unknown>"
    let targetModule := entry.directWrapperTargetModule.getD "<unknown>"
    output := output ++ s!"- `{entry.name}` → `{target}` — module `{entry.moduleName}`; target module: `{targetModule}`; compiled consumers: {entry.compiledConsumerCount}; single consumer: {entry.singleCompiledConsumer}; terminal: {entry.terminal}; cross-module: {entry.crossModuleDirectWrapper}\n"
  output := output ++ "\n## Priority private-consumer theorem review queue\n\n"
  output := output ++ "Each row is a public, non-simp, unresolved theorem whose sole compiled project-declaration consumer is private. This is a high-priority semantic-audit pool for public proof-routing helpers; it remains advisory because the theorem may still express an independently useful API result.\n\n"
  for entry in privateSingleConsumerReviewQueue do
    for consumer in entry.compiledConsumers do
      output := output ++ s!"- `{entry.name}` → `{consumer}` — module `{entry.moduleName}`; theorem dependents: {entry.dependents.size}; direct prerequisites: {entry.dependencies.size}; direct wrapper: {entry.directWrapperOf.isSome}\n"
  output := output ++ "\n## Multi-step single-consumer chains\n\n"
  output := output ++ "Each chain is maximal from a theorem with no single-consumer theorem predecessor. The final declaration may be a theorem, definition, or opaque declaration.\n\n"
  for chain in chains do
    output := output ++ s!"- {chainText chain}\n"
  output := output ++ "\n## Single-consumer theorem review queue\n\n"
  output := output ++ "Each row is `theorem → sole compiled consumer`. A consumer may be a theorem, definition, or opaque declaration. Declarations recorded in `notes/theorem-catalog-retained.md` are omitted from this queue.\n\n"
  for entry in singleConsumerReviewQueue do
    for consumer in entry.compiledConsumers do
      output := output ++ s!"- `{entry.name}` → `{consumer}` — module `{entry.moduleName}`; theorem dependents: {entry.dependents.size}; direct prerequisites: {entry.dependencies.size}; direct wrapper: {entry.directWrapperOf.isSome}\n"
  output := output ++ "\n## Priority terminal theorem review queue\n\n"
  output := output ++ "These terminal theorems are neither documented as completed nor retained and have no compiled project-declaration consumer. Source search is still required before removal.\n\n"
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
      ("compiledConsumers", .arr <| entry.compiledConsumers.map Json.str),
      ("compiledConsumerCount", .num entry.compiledConsumerCount),
      ("singleCompiledConsumer", .bool entry.singleCompiledConsumer),
      ("soleCompiledConsumerPrivate", .bool entry.soleCompiledConsumerPrivate),
      ("simpLemma", .bool entry.simpLemma),
      ("terminal", .bool entry.terminal),
      ("axioms", .arr <| entry.axioms.map Json.str),
      ("standardAxioms", .arr <| entry.standardAxioms.map Json.str),
      ("projectAxioms", .arr <| entry.projectAxioms.map Json.str),
      ("externalAxioms", .arr <| entry.externalAxioms.map Json.str),
      ("directWrapperOf", entry.directWrapperOf.map Json.str |>.getD .null),
      ("directWrapperTargetModule", entry.directWrapperTargetModule.map Json.str |>.getD .null),
      ("crossModuleDirectWrapper", .bool entry.crossModuleDirectWrapper),
      ("completedMention", .bool entry.completedMention),
      ("retainedMention", .bool entry.retainedMention)
    ]

run_cmd do
  let projectAxioms ← collectProjectAxioms
  let (entries, projectTheorems, theoremDependents) ← collectEntries projectAxioms
  let compiledConsumers ← collectCompiledConsumers projectTheorems
  let completed ← liftIO <| IO.FS.readFile ("notes" / "completed.md")
  let retained ← liftIO <| IO.FS.readFile ("notes" / "theorem-catalog-retained.md")
  let catalog := annotateEntries entries theoremDependents compiledConsumers completed retained
  let retainedEntries := catalog.filter fun entry => entry.retainedMention
  let terminals := terminalEntries catalog
  let completedTerminals := terminals.filter fun entry => entry.completedMention
  let retainedTerminals := terminals.filter fun entry => entry.retainedMention
  let reviewQueue :=
    terminals.filter fun entry => !entry.completedMention && !entry.retainedMention
  let priorityReviewQueue := compiledConsumerFreeEntries reviewQueue
  let singleConsumerEntries := singleCompiledConsumerEntries catalog
  let retainedSingleConsumers :=
    singleConsumerEntries.filter fun entry => entry.retainedMention
  let singleConsumerReviewQueue :=
    singleConsumerEntries.filter fun entry => !entry.retainedMention
  let privateSingleConsumerReviewQueue := privateSingleConsumerReviewEntries catalog
  let directWrappers := directWrapperEntries catalog
  let retainedDirectWrappers :=
    directWrappers.filter fun entry => entry.retainedMention
  let directWrapperReviewQueue :=
    directWrappers.filter fun entry => !entry.retainedMention
  let crossModuleDirectWrappers :=
    directWrappers.filter fun entry => entry.crossModuleDirectWrapper
  let crossModuleDirectWrapperReviewQueue :=
    directWrapperReviewQueue.filter fun entry => entry.crossModuleDirectWrapper
  let chains := singleConsumerChains catalog
  let terminalsWithCompiledConsumers :=
    terminals.filter fun entry => !entry.compiledConsumers.isEmpty
  let projectAxiomEntries := catalog.filter fun entry => !entry.projectAxioms.isEmpty
  let externalAxiomEntries := catalog.filter fun entry => !entry.externalAxioms.isEmpty
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorems.md") (markdown catalog chains)
  liftIO <| IO.FS.writeFile (outputDir / "theorems.json") (json catalog).pretty
  logInfo m!"Generated theorem catalog with {catalog.size} declarations, {dependencyEdgeCount catalog} dependency edges, and {terminals.size} terminal theorems ({retainedEntries.size} retained audit declarations; {completedTerminals.size} terminal theorems mentioned in completed.md; {retainedTerminals.size} retained terminal theorems; {terminalsWithCompiledConsumers.size} terminal theorems with compiled project consumers; {priorityReviewQueue.size} priority terminal review candidates; {retainedSingleConsumers.size} retained single-consumer theorems; {singleConsumerReviewQueue.size} single-consumer review candidates; {privateSingleConsumerReviewQueue.size} priority public non-simp theorems with sole private compiled consumers; {projectAxiomEntries.size} theorems depending on project axioms; {externalAxiomEntries.size} theorems depending on external nonstandard axioms; {directWrappers.size} direct-wrapper candidates; {retainedDirectWrappers.size} retained direct-wrapper candidates; {directWrapperReviewQueue.size} direct-wrapper review candidates; {crossModuleDirectWrappers.size} cross-module direct-wrapper candidates; {crossModuleDirectWrapperReviewQueue.size} cross-module direct-wrapper review candidates; {chains.size} multi-step single-consumer chains)"

end LeanCondensedMatter.TheoremCatalog