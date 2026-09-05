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

private def dependencyEdgeCount (entries : Array Entry) : Nat :=
  entries.foldl (init := 0) fun count entry => count + entry.dependencies.size

private def markdown (entries : Array Entry) : String := Id.run do
  let mut output := "# LeanCondensedMatter theorem catalog\n\n"
  output := output ++ "This file is generated from source-declared theorems in LeanCondensedMatter modules. Do not edit it manually.\n\n"
  output := output ++ "The JSON catalog also records direct dependencies between cataloged project theorems, extracted from compiled proof terms.\n\n"
  output := output ++ s!"Theorems: {entries.size}\n\n"
  output := output ++ s!"Dependency edges: {dependencyEdgeCount entries}\n\n"
  for entry in entries do
    output := output ++ s!"## `{entry.name}`\n\n"
    output := output ++ s!"Module: `{entry.moduleName}`\n\n"
    output := output ++ s!"```lean\n{entry.statement}\n```\n\n"
    if let some docString := entry.docString then
      output := output ++ docString.trimAscii.toString ++ "\n\n"
  return output

private def json (entries : Array Entry) : Json :=
  .arr <| entries.map fun entry =>
    .mkObj [
      ("name", .str entry.name),
      ("module", .str entry.moduleName),
      ("statement", .str entry.statement),
      ("docString", entry.docString.map Json.str |>.getD .null),
      ("dependencies", .arr <| entry.dependencies.map Json.str)
    ]

run_cmd do
  let entries ← collectEntries
  let outputDir : System.FilePath := "docs" / "generated"
  liftIO <| IO.FS.createDirAll outputDir
  liftIO <| IO.FS.writeFile (outputDir / "theorems.md") (markdown entries)
  liftIO <| IO.FS.writeFile (outputDir / "theorems.json") (json entries).pretty
  logInfo m!"Generated theorem catalog with {entries.size} declarations and {dependencyEdgeCount entries} dependency edges"

end LeanCondensedMatter.TheoremCatalog
