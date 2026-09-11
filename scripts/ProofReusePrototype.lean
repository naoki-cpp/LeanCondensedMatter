import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import Mathlib.Tactic.ClickSuggestions.FindPremises

open Lean Meta Elab Command
open Lean.Meta.RefinedDiscrTree
open Mathlib.Tactic.ClickSuggestions

namespace LeanCondensedMatter.ProofReusePrototype

structure ProjectTheorem where
  name : Name
  type : Expr
  moduleName : Name
  start? : Option Position
  usedConstants : NameSet

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.getRoot == Name.mkSimple "LeanCondensedMatter"

private def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

private partial def collectConstants (expr : Expr) (seen : NameSet := {}) : NameSet :=
  match expr with
  | .const name _ => seen.insert name
  | .app fn arg => collectConstants arg (collectConstants fn seen)
  | .lam _ type body _ => collectConstants body (collectConstants type seen)
  | .forallE _ type body _ => collectConstants body (collectConstants type seen)
  | .letE _ type value body _ =>
      collectConstants body (collectConstants value (collectConstants type seen))
  | .mdata _ body => collectConstants body seen
  | .proj _ _ body => collectConstants body seen
  | _ => seen

private def collectProjectTheorems : CommandElabM (Array ProjectTheorem) := do
  let env ← getEnv
  let mut theorems := #[]
  for (declName, info) in env.constants.toList do
    let .thmInfo theoremInfo := info | continue
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    let some ranges ← findDeclarationRanges? declName | continue
    theorems := theorems.push {
      name := declName
      type := theoremInfo.type
      moduleName
      start? := ranges.selectionRange.pos
      usedConstants := collectConstants theoremInfo.value
    }
  return theorems

private def indexKeys (conclusion : Expr) : Array Expr :=
  match conclusion.eq? with
  | some (_, lhs, _) => #[conclusion, lhs]
  | none => #[conclusion]

private def buildProjectTree (theorems : Array ProjectTheorem) :
    MetaM (RefinedDiscrTree Name) := do
  let mut pre : PreDiscrTree Name := {}
  for entry in theorems do
    setMCtx {}
    let (_, _, conclusion) ← forallMetaTelescope entry.type
    for indexed in indexKeys conclusion do
      for (key, lazy) in (← initializeLazyEntryWithEta indexed) do
        pre := pre.push key (lazy, entry.name)
  return pre.toRefinedDiscrTree

private def positionLt (left right : Position) : Bool :=
  left.line < right.line || (left.line == right.line && left.column < right.column)

private partial def importClosureLoop
    (env : Environment) (pending : List Name) (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | moduleName :: rest =>
      if seen.contains moduleName then
        importClosureLoop env rest seen
      else
        let seen := seen.insert moduleName
        match env.getModuleIdx? moduleName with
        | none => importClosureLoop env rest seen
        | some idx =>
            match env.header.moduleData[idx.toNat]? with
            | none => importClosureLoop env rest seen
            | some data =>
                let imports := data.imports.toList.map (·.module)
                importClosureLoop env (imports ++ rest) seen

private def importClosure (env : Environment) (moduleName : Name) : NameSet :=
  importClosureLoop env [moduleName] {}

private def visibleFrom
    (env : Environment) (subject candidate : ProjectTheorem) : Bool :=
  if subject.moduleName == candidate.moduleName then
    match candidate.start?, subject.start? with
    | some candidateStart, some subjectStart => positionLt candidateStart subjectStart
    | _, _ => false
  else
    (importClosure env subject.moduleName).contains candidate.moduleName

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
    (env : Environment) (subject : ProjectTheorem) (theorems : Array ProjectTheorem)
    (tree : RefinedDiscrTree Name) (filterExisting : Bool) : MetaM (Array (Name × Nat)) := do
  let subjectConst ← mkConstWithFreshMVarLevels subject.name
  let subjectType ← inferType subjectConst
  let syntheticGoal ← mkFreshExprSyntheticOpaqueMVar subjectType
  let (_, goal) ← syntheticGoal.mvarId!.intros
  goal.withContext do
    let target ← goal.getType
    let byName := theorems.foldl (init := NameMap.empty) fun map entry => map.insert entry.name entry
    let mut seen := NameSet.empty
    let mut results := #[]
    for query in indexKeys target do
      let matchResult ← getMatches tree query
      for group in matchResult.flatten do
        for candidateName in group do
          if candidateName == subject.name || seen.contains candidateName then
            continue
          seen := seen.insert candidateName
          let some candidate := byName.find? candidateName | continue
          if filterExisting then
            unless visibleFrom env subject candidate do continue
            if subject.usedConstants.contains candidateName then continue
          if let some premiseGoals ← tryCandidate goal candidateName then
            results := results.push (candidateName, premiseGoals)
    return results

private def runProofReuse (id : Syntax) (filterExisting : Bool) : CommandElabM Unit := do
  let subjectName ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let theorems ← collectProjectTheorems
  let some subject := theorems.find? (·.name == subjectName) |
    throwError "{subjectName} is not a source theorem in LeanCondensedMatter"
  let results ← liftTermElabM do
    let tree ← buildProjectTree theorems
    findReuse env subject theorems tree filterExisting
  if results.isEmpty then
    logInfo m!"{subjectName}: no project theorem reuse found"
  else
    let lines := results.toList.take 20 |>.map fun (candidate, premiseGoals) =>
      let mode := if premiseGoals == 0 then "apply" else "apply + assumptions"
      s!"{candidate} ({mode})"
    logInfo m!"{subjectName}:\n{String.intercalate "\n" lines}"

syntax (name := proofReuseCmd) "#proof_reuse " ident : command
syntax (name := proofReuseRawCmd) "#proof_reuse_raw " ident : command

elab_rules : command
  | `(#proof_reuse $id:ident) => runProofReuse id true
  | `(#proof_reuse_raw $id:ident) => runProofReuse id false

#proof_reuse_raw SecondQuantization.Bosonic.create_basisState_eq
#proof_reuse SecondQuantization.Bosonic.create_basisState_eq
#proof_reuse SecondQuantization.Bosonic.create_basisState

end LeanCondensedMatter.ProofReusePrototype
