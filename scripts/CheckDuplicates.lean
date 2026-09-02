import Lean
import LeanCondensedMatter

open Lean Elab Command

namespace LeanCondensedMatter.CheckDuplicates

inductive Kind where
  | theorem
  | definition
  deriving BEq

structure Entry where
  name : Name
  kind : Kind
  levelParams : List Name
  type : Expr
  value : Option Expr := none

structure CanonicalEntry where
  name : Name
  kind : Kind
  type : Expr
  value : Option Expr := none

private def projectModule? (moduleName : Name) : Bool :=
  moduleName.getRoot == Name.mkSimple "LeanCondensedMatter"

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

private def collectEntries : CommandElabM (Array Entry) := do
  let env ← getEnv
  let mut entries := #[]
  for (declName, info) in env.constants.toList do
    let some moduleName := declarationModule? env declName | continue
    unless projectModule? moduleName do continue
    -- Keep only user-facing source declarations. Lean's own predicate removes private/internal
    -- names, macro-generated declarations, reserved names, auxiliary recursors, and similar
    -- automatically generated declarations.
    if ← liftCoreM <| isAutoDeclOrPrivate_Internal declName then continue
    -- A `local instance` leaves behind its declaration and instance-reducible status in the
    -- imported environment, but its local instance entry itself is deliberately not exported.
    -- Exclude those file-local typeclass helpers while retaining global and scoped instances.
    if localInstanceDeclaration? env declName then continue
    unless (← findDeclarationRanges? declName).isSome do continue
    match info with
    | .thmInfo theoremInfo =>
        entries := entries.push {
          name := declName
          kind := .theorem
          levelParams := theoremInfo.levelParams
          type := theoremInfo.type
        }
    | .defnInfo definitionInfo =>
        entries := entries.push {
          name := declName
          kind := .definition
          levelParams := definitionInfo.levelParams
          type := definitionInfo.type
          value := some definitionInfo.value
        }
    | .opaqueInfo opaqueInfo =>
        entries := entries.push {
          name := declName
          kind := .definition
          levelParams := opaqueInfo.levelParams
          type := opaqueInfo.type
          value := some opaqueInfo.value
        }
    | _ => continue
  return entries

private def canonicalLevels : List Name → Nat → List Level
  | [], _ => []
  | _ :: rest, i =>
      .param (Name.mkSimple ("_dup_u_" ++ toString i)) :: canonicalLevels rest (i + 1)

private def canonicalize (entry : Entry) : CanonicalEntry :=
  let levels := canonicalLevels entry.levelParams 0
  {
    name := entry.name
    kind := entry.kind
    type := entry.type.instantiateLevelParams entry.levelParams levels
    value := entry.value.map fun value =>
      value.instantiateLevelParams entry.levelParams levels
  }

private def kindLess : Kind → Kind → Bool
  | .theorem, .definition => true
  | _, _ => false

private def optionExprLess : Option Expr → Option Expr → Bool
  | none, some _ => true
  | some left, some right => Expr.lt left right
  | _, _ => false

private def canonicalLess (left right : CanonicalEntry) : Bool :=
  if left.kind != right.kind then
    kindLess left.kind right.kind
  else if Expr.lt left.type right.type then
    true
  else if Expr.lt right.type left.type then
    false
  else
    optionExprLess left.value right.value

private def sameCanonical (left right : CanonicalEntry) : Bool :=
  left.kind == right.kind &&
    Expr.eqv left.type right.type &&
    match left.value, right.value with
    | none, none => true
    | some leftValue, some rightValue => Expr.eqv leftValue rightValue
    | _, _ => false

private structure Duplicate where
  kind : Kind
  left : Name
  right : Name

private def findDuplicates (entries : Array Entry) : Array Duplicate := Id.run do
  let sorted := entries.map canonicalize |>.qsort canonicalLess
  let mut previous : Option CanonicalEntry := none
  let mut duplicates : Array Duplicate := #[]
  for current in sorted do
    match previous with
    | some prior =>
        if sameCanonical prior current then
          duplicates := duplicates.push {
            kind := current.kind
            left := prior.name
            right := current.name
          }
    | none => pure ()
    previous := some current
  return duplicates

private def kindLabel : Kind → String
  | .theorem => "theorem"
  | .definition => "definition"

elab "assert_project_no_duplicate_declarations" : command => do
  let entries ← collectEntries
  let duplicates := findDuplicates entries
  unless duplicates.isEmpty do
    for duplicate in duplicates do
      logError m!"duplicate {kindLabel duplicate.kind}: {.ofConstName duplicate.left} and {.ofConstName duplicate.right}"
    throwError "found {duplicates.size} exact duplicate LeanCondensedMatter declaration pairs"
  logInfo m!"Checked {entries.size} user-facing source declarations; no exact duplicate theorem or definition pairs found."

assert_project_no_duplicate_declarations

end LeanCondensedMatter.CheckDuplicates
