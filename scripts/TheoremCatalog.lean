import Lean
import LeanCondensedMatter

open Lean Elab Command Meta

namespace LeanCondensedMatter.TheoremCatalog

structure Candidate where
  name : Name
  moduleName : Name
  theoremInfo : TheoremVal

structure Entry where
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

private def directProjectTheoremDependencies
    (projectTheorems : NameSet) (declName : Name) (value : Expr) : Array String :=
  (value.foldConsts #[] fun dependency dependencies =>
    if dependency != declName && projectTheorems.contains dependency then
      dependencies.push dependency.toString
    else
      dependencies).qsort fun left right => left < right

private def collectEntries : CommandElabM (Array Entry) := do
  let env ← getEnv
  let (candidates, projectTheorems) ← collectCandidates
  let mut entries := #[]
  for candidate in candidates do
    let statement ← liftTermElabM do
      return (← ppExpr candidate.theoremInfo.type).pretty
    let docString ← liftIO <| findDocString? env candidate.name
    entries := entries.push {
      name := candidate.name.toString
      moduleName := candidate.moduleName.toString
      statement
      docString
      dependencies := directProjectTheoremDependencies
        projectTheorems candidate.name candidate.theoremInfo.value
    }
  return entries.qsort fun left right => left.name < right.name

private def directProjectTheoremDependents
    (entries : Array Entry) (declName : String) : Array String :=
  entries.foldl (init := #[]) fun dependents entry =>
    if entry.dependencies.contains declName then
      dependents.push entry.name
    else
      dependents

private def containsSubstring (text pattern : String) : Bool :=
  (text.find? pattern).isSome

private def declarationBaseName (declName : String) : String :=
  (declName.splitOn ".").getLastD declName

private def mentionedInCompleted (completed declName : String) : Bool :=
  containsSubstring completed declName ||
    containsSubstring completed s!"`{declarationBaseName declName}`"

private def annotateEntries
    (entries : Array Entry) (completed : String) : Array CatalogEntry :=
  entries.map fun entry =>
    let dependents := directProjectTheoremDependents entries entry.name
    let terminal := dependents.isEmpty
    {
      name := entry.name
      moduleName := entry.moduleName
      statement := entry.statement
      docString := entry.docString
      dependencies := entry.dependencies
      dependents
      terminal
      completedMention := terminal && mentionedInCompleted completed entry.name
    }

private def dependencyEdgeCount (entries : Array CatalogEntry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.dependencies.size

private def terminalEntries (entries : Array CatalogEntry) : Array CatalogEntry :=
  entries.filter fun entry => entry.terminal

private def markdown (entries : Array CatalogEntry) : String := Id.run do
  let terminals := terminalEntries entries
  let completedTerminals := terminals.filter fun entry => entry.completedMention
  let reviewQueue := terminals.filter fun entry => !entry.completedMention
  let mut output := "# LeanCondensedMatter theorem catalog\n\n"
  output := output ++ "This file is generated from source-declared theorems in LeanCondensedMatter modules. Do not edit it manually.\n\n"
  output := output ++ "The JSON catalog records direct dependencies and direct dependents between cataloged project theorems, extracted from compiled proof terms.\n\n"
  output := output ++ s!"Theorems: {entries.size}\n\n"
  output := output ++ s!"Dependency edges: {dependencyEdgeCount entries}\n\n"
  output := output ++ s!"Terminal theorems: {terminals.size}\n\n"
  output := output ++ s!"Terminal theorems mentioned in completed.md: {completedTerminals.size}\n\n"
  output := output ++ s!"Terminal theorem review queue: {reviewQueue.size}\n\n"
  output := output ++ "Here a terminal theorem means a theorem with no direct project-theorem dependents: no other source-declared project theorem in the catalog uses it. This is the endpoint side of the proof graph, not the prerequisite-free side.\n\n"
  output := output ++ "A mention in `notes/completed.md` is evidence that the endpoint is an intentional completed result. Every other terminal theorem remains a semantic review candidate: compare its statement and module with `notes/roadmap.md` and the detailed roadmaps to decide whether it is a roadmap intermediate that still needs a consumer, an intentional local endpoint, or an unnecessary public theorem.\n\n"
  output := output ++ "## Terminal theorem review queue\n\n"
  for entry in reviewQueue do
    output := output ++ s!"- `{entry.name}` — module `{entry.moduleName}`; direct prerequisites: {entry.dependencies.size}\n"
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
      ("terminal", .bool entry.terminal),
      ("completedMention", .bool entry.completedMention)
    ]

run_cmd do
  let entries ← collectEntries
  let completed ← liftIO <| IO.FS.readFile ("notes" / "completed.md")
  let catalog := annotateEntries entries completed
  let terminals := terminalEntries catalog
  let completedTerminals := terminals.filter fun entry => entry.completedMention
  let reviewQueue := terminals.filter fun entry => !entry.completedMention
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorems.md") (markdown catalog)
  liftIO <| IO.FS.writeFile (outputDir / "theorems.json") (json catalog).pretty
  logInfo m!"Generated theorem catalog with {catalog.size} declarations, {dependencyEdgeCount catalog} dependency edges, and {terminals.size} terminal theorems ({completedTerminals.size} mentioned in completed.md; {reviewQueue.size} queued for review)"

end LeanCondensedMatter.TheoremCatalog
