import Lean
import LeanCondensedMatter

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

structure CatalogEntry where
  name : String
  moduleName : String
  statement : String
  docString : Option String
  dependencies : Array String
  dependents : Array String
  compiledConsumers : Array String
  terminal : Bool
  completedMention : Bool

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

private def directProjectTheoremDependencyNames
    (projectTheorems : NameSet) (declName : Name) (value : Expr) : Array Name :=
  value.foldConsts #[] fun dependency dependencies =>
    if dependency != declName && projectTheorems.contains dependency then
      dependencies.push dependency
    else
      dependencies

private def sortedNameStrings (names : Array Name) : Array String :=
  (names.map fun name => name.toString).qsort fun left right => left < right

private def addConsumer
    (consumers : NameMap (Array String)) (dependency : Name) (consumer : String) :
    NameMap (Array String) :=
  let existing := (consumers.find? dependency).getD #[]
  consumers.insert dependency (existing.push consumer)

private def collectEntries :
    CommandElabM (Array Entry × NameSet × NameMap (Array String)) := do
  let env ← getEnv
  let (candidates, projectTheorems) ← collectCandidates
  let mut entries := #[]
  let mut theoremDependents : NameMap (Array String) := {}
  for candidate in candidates do
    let statement ← liftTermElabM do
      return (← ppExpr candidate.theoremInfo.type).pretty
    let docString ← liftIO <| findDocString? env candidate.name
    let dependencyNames := directProjectTheoremDependencyNames
      projectTheorems candidate.name candidate.theoremInfo.value
    for dependency in dependencyNames do
      theoremDependents := addConsumer theoremDependents dependency candidate.name.toString
    entries := entries.push {
      declName := candidate.name
      name := candidate.name.toString
      moduleName := candidate.moduleName.toString
      statement
      docString
      dependencies := sortedNameStrings dependencyNames
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

private def containsSubstring (text pattern : String) : Bool :=
  (text.find? pattern).isSome

private def declarationBaseName (declName : String) : String :=
  (declName.splitOn ".").getLastD declName

private def mentionedInCompleted (completed declName : String) : Bool :=
  containsSubstring completed declName ||
    containsSubstring completed s!"`{declarationBaseName declName}`"

private def sortedConsumers
    (consumers : NameMap (Array String)) (declName : Name) : Array String :=
  ((consumers.find? declName).getD #[]).qsort fun left right => left < right

private def annotateEntries
    (entries : Array Entry)
    (theoremDependents compiledConsumers : NameMap (Array String))
    (completed : String) : Array CatalogEntry :=
  entries.map fun entry =>
    let dependents := sortedConsumers theoremDependents entry.declName
    let compiledConsumers := sortedConsumers compiledConsumers entry.declName
    let terminal := dependents.isEmpty
    {
      name := entry.name
      moduleName := entry.moduleName
      statement := entry.statement
      docString := entry.docString
      dependencies := entry.dependencies
      dependents
      compiledConsumers
      terminal
      completedMention := terminal && mentionedInCompleted completed entry.name
    }

private def dependencyEdgeCount (entries : Array CatalogEntry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.dependencies.size

private def terminalEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.terminal

private def compiledConsumerFreeEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.compiledConsumers.isEmpty

private def markdown (entries : Array CatalogEntry) : String := Id.run do
  let terminals := terminalEntries entries
  let completedTerminals := terminals.filter fun entry => entry.completedMention
  let reviewQueue := terminals.filter fun entry => !entry.completedMention
  let priorityReviewQueue := compiledConsumerFreeEntries reviewQueue
  let terminalsWithCompiledConsumers :=
    terminals.filter fun entry => !entry.compiledConsumers.isEmpty
  let mut output := "# LeanCondensedMatter theorem catalog\n\n"
  output := output ++ "This file is generated from source-declared theorems in LeanCondensedMatter modules. Do not edit it manually.\n\n"
  output := output ++ "The JSON catalog records direct theorem dependencies/dependents and compiled project-declaration consumers. Dependencies are extracted from compiled proof terms; compiled consumers additionally scan source-declared project theorem, definition, and opaque-declaration values.\n\n"
  output := output ++ s!"Theorems: {entries.size}\n\n"
  output := output ++ s!"Dependency edges: {dependencyEdgeCount entries}\n\n"
  output := output ++ s!"Terminal theorems: {terminals.size}\n\n"
  output := output ++ s!"Terminal theorems mentioned in completed.md: {completedTerminals.size}\n\n"
  output := output ++ s!"Terminal theorems with compiled project consumers: {terminalsWithCompiledConsumers.size}\n\n"
  output := output ++ s!"Terminal theorem review queue: {reviewQueue.size}\n\n"
  output := output ++ s!"Priority terminal review queue with no compiled project consumers: {priorityReviewQueue.size}\n\n"
  output := output ++ "Here a terminal theorem means a theorem with no direct project-theorem dependents: no other source-declared project theorem in the catalog retains it in its compiled proof term. This is the endpoint side of the theorem proof graph, not the prerequisite-free side.\n\n"
  output := output ++ "`compiledConsumers` is broader: it records source-declared project theorems, definitions, and opaque declarations whose compiled values retain a reference to the theorem. This catches uses such as theorem proofs stored inside definition fields. It is still not a source-level use analysis: simplification, unfolding, and definitional reduction can erase an explicit source reference before compilation. Therefore a theorem with no compiled consumer is only a higher-priority review candidate, never automatic evidence that the theorem is unused.\n\n"
  output := output ++ "A mention in `notes/completed.md` is evidence that the endpoint is an intentional completed result. Every other terminal theorem remains a semantic review candidate: compare its statement and module with `notes/roadmap.md` and the detailed roadmaps to decide whether it is a roadmap intermediate that still needs a consumer, an intentional local endpoint, or an unnecessary public theorem.\n\n"
  output := output ++ "## Priority terminal theorem review queue\n\n"
  output := output ++ "These terminal theorems are not mentioned in `completed.md` and have no compiled project-declaration consumer. Source search is still required before removal.\n\n"
  for entry in priorityReviewQueue do
    output := output ++ s!"- `{entry.name}` — module `{entry.moduleName}`; direct prerequisites: {entry.dependencies.size}\n"
  output := output ++ "\n## Full terminal theorem review queue\n\n"
  for entry in reviewQueue do
    output := output ++ s!"- `{entry.name}` — module `{entry.moduleName}`; direct prerequisites: {entry.dependencies.size}; compiled consumers: {entry.compiledConsumers.size}\n"
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
      ("terminal", .bool entry.terminal),
      ("completedMention", .bool entry.completedMention)
    ]

run_cmd do
  let (entries, projectTheorems, theoremDependents) ← collectEntries
  let compiledConsumers ← collectCompiledConsumers projectTheorems
  let completed ← liftIO <| IO.FS.readFile ("notes" / "completed.md")
  let catalog := annotateEntries entries theoremDependents compiledConsumers completed
  let terminals := terminalEntries catalog
  let completedTerminals := terminals.filter fun entry => entry.completedMention
  let reviewQueue := terminals.filter fun entry => !entry.completedMention
  let priorityReviewQueue := compiledConsumerFreeEntries reviewQueue
  let terminalsWithCompiledConsumers :=
    terminals.filter fun entry => !entry.compiledConsumers.isEmpty
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorems.md") (markdown catalog)
  liftIO <| IO.FS.writeFile (outputDir / "theorems.json") (json catalog).pretty
  logInfo m!"Generated theorem catalog with {catalog.size} declarations, {dependencyEdgeCount catalog} dependency edges, and {terminals.size} terminal theorems ({completedTerminals.size} mentioned in completed.md; {terminalsWithCompiledConsumers.size} with compiled project consumers; {priorityReviewQueue.size} priority review candidates)"

end LeanCondensedMatter.TheoremCatalog
