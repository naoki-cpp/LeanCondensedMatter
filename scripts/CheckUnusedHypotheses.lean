import Lean
import LeanCondensedMatter

open Lean Elab Command Meta

namespace LeanCondensedMatter.CheckUnusedHypotheses

structure TheoremEntry where
  name : Name
  type : Expr
  value : Expr

structure Candidate where
  theoremName : Name
  binderName : Name
  binderIndex : Nat
  binderType : String

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.getRoot == Name.mkSimple "LeanCondensedMatter"

private def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

private def containsFVar (expr : Expr) (fvarId : FVarId) : Bool :=
  (expr.find? fun subexpr =>
    match subexpr with
    | .fvar id => id == fvarId
    | _ => false).isSome

private def collectTheorems : CommandElabM (Array TheoremEntry) := do
  let env ← getEnv
  let mut entries := #[]
  for (declName, info) in env.constants.toList do
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    if ← liftCoreM <| isAutoDeclOrPrivate_Internal declName then continue
    unless (← findDeclarationRanges? declName).isSome do continue
    match info with
    | .thmInfo theoremInfo =>
        entries := entries.push {
          name := declName
          type := theoremInfo.type
          value := theoremInfo.value
        }
    | _ => continue
  return entries

private def analyzeTheorem (entry : TheoremEntry) : MetaM (Array Candidate × Bool) := do
  forallTelescope entry.type fun typeArgs resultType => do
    lambdaTelescope entry.value fun proofArgs proofBody => do
      if typeArgs.size != proofArgs.size then
        return (#[], false)

      let mut candidates := #[]
      for i in List.range typeArgs.size do
        let typeArg := typeArgs[i]!
        let typeDecl ← typeArg.fvarId!.getDecl
        unless ← isProp typeDecl.type do continue

        let typeFVarId := typeArg.fvarId!
        let mut requiredByType := containsFVar resultType typeFVarId
        unless requiredByType do
          for j in List.range typeArgs.size do
            if i < j then
              let laterDecl ← typeArgs[j]!.fvarId!.getDecl
              if containsFVar laterDecl.type typeFVarId then
                requiredByType := true
                break
        if requiredByType then continue

        let proofFVarId := proofArgs[i]!.fvarId!
        if containsFVar proofBody proofFVarId then continue

        let binderType := (← ppExpr typeDecl.type).pretty.replace "\n" " "
        candidates := candidates.push {
          theoremName := entry.name
          binderName := typeDecl.userName
          binderIndex := i
          binderType
        }
      return (candidates, true)

private def candidateLess (left right : Candidate) : Bool :=
  let leftName := left.theoremName.toString
  let rightName := right.theoremName.toString
  if leftName != rightName then
    decide (leftName < rightName)
  else
    decide (left.binderIndex < right.binderIndex)

private def renderMarkdown
    (theoremCount mismatchCount : Nat) (candidates : Array Candidate) : String := Id.run do
  let mut lines := #[
    "## Potentially unused theorem hypotheses",
    "",
    s!"Scanned {theoremCount} user-facing project theorems. Found {candidates.size} structurally unused `Prop` hypotheses."
  ]
  if mismatchCount > 0 then
    lines := lines.push s!"Skipped {mismatchCount} theorems whose proof telescope did not match the theorem telescope."
  lines := lines.push ""
  lines := lines.push "A hypothesis is reported only when it is absent from the theorem conclusion, all later binder types, and the elaborated proof body. This is an advisory structural audit; reported hypotheses are candidates for theorem generalization, not an automatic API change."
  lines := lines.push ""
  if candidates.isEmpty then
    lines := lines.push "No candidates found."
  else
    for candidate in candidates do
      lines := lines.push s!"- `{candidate.theoremName}`: `{candidate.binderName}` : `{candidate.binderType}`"
  return String.intercalate "\n" lines.toList ++ "\n"

elab "audit_project_unused_hypotheses" : command => do
  let theorems ← collectTheorems
  let mut candidates := #[]
  let mut mismatchCount := 0
  for theoremEntry in theorems do
    let (theoremCandidates, matched) ← liftTermElabM <| analyzeTheorem theoremEntry
    if !matched then
      mismatchCount := mismatchCount + 1
    for candidate in theoremCandidates do
      candidates := candidates.push candidate

  let candidates := candidates.qsort candidateLess
  let markdown := renderMarkdown theorems.size mismatchCount candidates
  liftIO <| IO.FS.writeFile "unused-hypotheses.md" markdown
  logInfo m!"Unused-hypothesis audit: {candidates.size} candidates across {theorems.size} user-facing theorems; {mismatchCount} telescope mismatches skipped."

audit_project_unused_hypotheses

end LeanCondensedMatter.CheckUnusedHypotheses
