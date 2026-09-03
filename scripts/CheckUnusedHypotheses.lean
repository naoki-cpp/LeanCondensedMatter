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

private def analyzeTheorem (entry : TheoremEntry) : MetaM (Array Candidate) := do
  forallTelescope entry.type fun typeArgs resultType => do
    -- Apply the elaborated proof to the theorem binders and weak-head normalize it. This avoids
    -- assuming that the stored proof is syntactically a lambda telescope: eta-reduced proofs,
    -- leading lets, and similar elaboration details can otherwise make the two telescopes differ.
    let proofBody ← whnf (mkAppN entry.value typeArgs)
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

      if containsFVar proofBody typeFVarId then continue

      let binderType := (← ppExpr typeDecl.type).pretty.replace "\n" " "
      candidates := candidates.push {
        theoremName := entry.name
        binderName := typeDecl.userName
        binderIndex := i
        binderType
      }
    return candidates

private def candidateLess (left right : Candidate) : Bool :=
  let leftName := left.theoremName.toString
  let rightName := right.theoremName.toString
  if leftName != rightName then
    decide (leftName < rightName)
  else
    decide (left.binderIndex < right.binderIndex)

private def renderMarkdown (theoremCount : Nat) (candidates : Array Candidate) : String := Id.run do
  let mut lines := #[
    "## Potentially unused theorem hypotheses",
    "",
    s!"Scanned {theoremCount} user-facing project theorems. Found {candidates.size} structurally unused `Prop` hypotheses.",
    "",
    "A hypothesis is reported only when it is absent from the theorem conclusion, all later binder types, and the weak-head-normalized elaborated proof body. This is an advisory structural audit; reported hypotheses are candidates for theorem generalization, not an automatic API change.",
    ""
  ]
  if candidates.isEmpty then
    lines := lines.push "No candidates found."
  else
    for candidate in candidates do
      lines := lines.push s!"- `{candidate.theoremName}`: `{candidate.binderName}` : `{candidate.binderType}`"
  return String.intercalate "\n" lines.toList ++ "\n"

elab "audit_project_unused_hypotheses" : command => do
  let theorems ← collectTheorems
  let mut candidates := #[]
  for theoremEntry in theorems do
    let theoremCandidates ← liftTermElabM <| analyzeTheorem theoremEntry
    for candidate in theoremCandidates do
      candidates := candidates.push candidate

  let sortedCandidates := candidates.qsort candidateLess
  let markdown := renderMarkdown theorems.size sortedCandidates
  liftIO <| IO.FS.writeFile "unused-hypotheses.md" markdown
  for candidate in sortedCandidates do
    logInfo m!"potentially unused hypothesis: {candidate.theoremName}.{candidate.binderName} : {candidate.binderType}"
  logInfo m!"Unused-hypothesis audit: {sortedCandidates.size} candidates across {theorems.size} user-facing theorems."

audit_project_unused_hypotheses

end LeanCondensedMatter.CheckUnusedHypotheses
