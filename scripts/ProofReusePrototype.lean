import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import Mathlib.Tactic.ClickSuggestions.FindPremises

open Lean Meta Elab Command
open Lean.Meta.RefinedDiscrTree
open Mathlib.Tactic.ClickSuggestions

namespace LeanCondensedMatter.ProofReusePrototype

structure ProjectTheorem where
  name : Name
  type : Expr

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.getRoot == Name.mkSimple "LeanCondensedMatter"

private def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

private def collectProjectTheorems : CommandElabM (Array ProjectTheorem) := do
  let env ← getEnv
  let mut theorems := #[]
  for (declName, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    unless (← findDeclarationRanges? declName).isSome do continue
    theorems := theorems.push { name := declName, type := theoremInfo.type }
  return theorems

private def buildProjectTree (theorems : Array ProjectTheorem) :
    MetaM (RefinedDiscrTree Name) := do
  let mut pre : PreDiscrTree Name := {}
  for entry in theorems do
    setMCtx {}
    let (_, _, conclusion) ← forallMetaTelescope entry.type
    for (key, lazy) in (← initializeLazyEntryWithEta conclusion) do
      pre := pre.push key (lazy, entry.name)
  return pre.toRefinedDiscrTree

private def tryCandidate (goal : MVarId) (candidate : Name) : MetaM (Option Nat) := do
  let saved ← saveState
  try
    let proof ← mkConstWithFreshMVarLevels candidate
    let subgoals ← goal.apply proof
    let mut closes := true
    for subgoal in subgoals do
      unless ← subgoal.assumptionCore do
        closes := false
    let result := if closes then some subgoals.length else none
    saved.restore
    return result
  catch _ =>
    saved.restore
    return none

private def findReuse
    (subject : Name) (tree : RefinedDiscrTree Name) : MetaM (Array (Name × Nat)) := do
  let subjectConst ← mkConstWithFreshMVarLevels subject
  let subjectType ← inferType subjectConst
  let syntheticGoal ← mkFreshExprSyntheticOpaqueMVar subjectType
  let (_, goal) ← syntheticGoal.mvarId!.intros
  goal.withContext do
    let target ← goal.getType
    let matchResult ← getMatches tree target
    let mut seen := NameSet.empty
    let mut results := #[]
    for group in matchResult.flatten do
      for candidate in group do
        if candidate == subject || seen.contains candidate then
          continue
        seen := seen.insert candidate
        if let some premiseGoals ← tryCandidate goal candidate then
          results := results.push (candidate, premiseGoals)
    return results

syntax (name := proofReuseCmd) "#proof_reuse " ident : command

elab_rules : command
  | `(#proof_reuse $id:ident) => do
      let subject ← resolveGlobalConstNoOverload id
      let theorems ← collectProjectTheorems
      let results ← liftTermElabM do
        let tree ← buildProjectTree theorems
        findReuse subject tree
      if results.isEmpty then
        logInfo m!"{subject}: no project theorem reuse found"
      else
        let lines := results.toList.take 20 |>.map fun (candidate, premiseGoals) =>
          let mode := if premiseGoals == 0 then "apply" else "apply + assumptions"
          s!"{candidate} ({mode})"
        logInfo m!"{subject}:\n{String.intercalate "\n" lines}"

#proof_reuse SecondQuantization.Bosonic.create_basisState_eq

end LeanCondensedMatter.ProofReusePrototype
