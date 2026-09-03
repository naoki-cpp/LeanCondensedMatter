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

private def collectTheorems : CommandElabM (Array TheoremEntry) := do
  let env ← getEnv
  let mut entries := #[]
  for (declName, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    if ← liftCoreM <| isAutoDeclOrPrivate_Internal declName then continue
    unless (← findDeclarationRanges? declName).isSome do continue
    entries := entries.push {
      name := declName
      type := theoremInfo.type
      value := theoremInfo.value
    }
  return entries

private def analyzeTheorem (entry : TheoremEntry) : MetaM (Array Candidate × Bool) := do
  forallTelescope entry.type fun typeArgs resultType => do
    lambdaTelescope entry.value fun proofArgs proofBody => do
      -- Scan the proof body once. If the stored proof exposes fewer leading lambdas than the
      -- theorem type (for example because it is eta-reduced or starts with a non-lambda wrapper),
      -- unmatched binders are conservatively treated as used rather than forcing proof reduction.
      let proofFVars := (collectFVars {} proofBody).fvarSet
      let conservativeProofTail := proofArgs.size < typeArgs.size

      -- Scan result/later-binder dependencies once from right to left. Reusing CollectFVars.State
      -- also reuses its visited-expression set when binder types share subexpressions.
      let mut requiredByLater := collectFVars {} resultType
      let mut candidates := #[]
      for offset in List.range typeArgs.size do
        let i := typeArgs.size - 1 - offset
        let typeArg := typeArgs[i]!
        let typeDecl ← typeArg.fvarId!.getDecl
        let typeFVarId := typeArg.fvarId!
        let usedByType := requiredByLater.fvarSet.contains typeFVarId
        let usedByProof :=
          if h : i < proofArgs.size then
            proofFVars.contains proofArgs[i].fvarId!
          else
            true

        if !usedByType && !usedByProof && (← isProp typeDecl.type) then
          let binderType := (← ppExpr typeDecl.type).pretty.replace "\n" " "
          candidates := candidates.push {
            theoremName := entry.name
            binderName := typeDecl.userName
            binderIndex := i
            binderType
          }

        requiredByLater := collectFVars requiredByLater typeDecl.type
      return (candidates, conservativeProofTail)

private def candidateLess (left right : Candidate) : Bool :=
  let leftName := left.theoremName.toString
  let rightName := right.theoremName.toString
  if leftName != rightName then
    decide (leftName < rightName)
  else
    decide (left.binderIndex < right.binderIndex)

private def renderMarkdown
    (theoremCount conservativeProofCount : Nat) (candidates : Array Candidate) : String := Id.run do
  let mut lines := #[
    "## Potentially unused theorem hypotheses",
    "",
    s!"Scanned {theoremCount} user-facing project theorems. Found {candidates.size} structurally unused `Prop` hypotheses."
  ]
  if conservativeProofCount > 0 then
    lines := lines.push s!"For {conservativeProofCount} theorem proofs that exposed fewer leading lambdas than their theorem types, unmatched binders were conservatively treated as used."
  lines := lines.push ""
  lines := lines.push "A hypothesis is reported only when it is absent from the theorem conclusion, all later binder types, and the elaborated proof body. The audit scans each proof and theorem-type dependency structure once and does not unfold theorem bodies. This is advisory: reported hypotheses are candidates for theorem generalization, not an automatic API change."
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
  let mut conservativeProofCount := 0
  for theoremEntry in theorems do
    let (theoremCandidates, conservativeProofTail) ← liftTermElabM <| analyzeTheorem theoremEntry
    if conservativeProofTail then
      conservativeProofCount := conservativeProofCount + 1
    for candidate in theoremCandidates do
      candidates := candidates.push candidate

  let sortedCandidates := candidates.qsort candidateLess
  let markdown := renderMarkdown theorems.size conservativeProofCount sortedCandidates
  liftIO <| IO.FS.writeFile "unused-hypotheses.md" markdown
  for candidate in sortedCandidates do
    logInfo m!"potentially unused hypothesis: {candidate.theoremName}.{candidate.binderName} : {candidate.binderType}"
  logInfo m!"Unused-hypothesis audit: {sortedCandidates.size} candidates across {theorems.size} user-facing theorems; {conservativeProofCount} proofs handled conservatively."

audit_project_unused_hypotheses

end LeanCondensedMatter.CheckUnusedHypotheses
