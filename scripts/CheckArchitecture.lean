import Lean
import LeanCondensedMatter
import Lean.Elab.Command
import Lean.Util.FoldConsts

open Lean Elab Command

namespace LeanCondensedMatter.ArchitectureAudit

/-- One compiled declaration owned by a `LeanCondensedMatter` source module. -/
structure ProjectDeclaration where
  name : Name
  moduleName : Name
  sourceDeclared : Bool

/-- Read-only compiled project state shared by all semantic architecture checks. -/
structure Snapshot where
  env : Environment
  declarations : Array ProjectDeclaration

/-- A named semantic architecture check. Checks are pure over one compiled snapshot so they can
accumulate violations instead of aborting on the first failure. -/
structure NamedCheck where
  name : String
  run : Snapshot → Array String

/-- Module-boundary-aware prefix matching for Lean names. -/
def nameMatchesPrefix (name expectedPrefix : Name) : Bool :=
  let nameString := name.toString
  let prefixString := expectedPrefix.toString
  nameString == prefixString || nameString.startsWith (prefixString ++ ".")

/-- Whether a module belongs to this project rather than Mathlib or another dependency. -/
def isProjectModule (moduleName : Name) : Bool :=
  moduleName.getRoot.toString == "LeanCondensedMatter"

/-- Resolve a compiled declaration to the module that owns it. -/
def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

/-- Capture project declarations once from the compiled environment. Generated declarations are
retained but marked with `sourceDeclared = false`; checks that model source ownership can filter
them without reparsing Lean syntax. -/
def collectSnapshot : CommandElabM Snapshot := do
  let env ← getEnv
  let mut declarations : Array ProjectDeclaration := #[]
  for (declName, _) in env.constants.toList do
    let some moduleName := declarationModule? env declName | continue
    unless isProjectModule moduleName do continue
    let sourceDeclared := (← findDeclarationRanges? declName).isSome
    declarations := declarations.push {
      name := declName
      moduleName := moduleName
      sourceDeclared := sourceDeclared
    }
  return { env, declarations }

/-- Find one compiled project declaration by name. -/
def Snapshot.findDeclaration? (snapshot : Snapshot) (declName : Name) : Option ProjectDeclaration :=
  snapshot.declarations.find? fun declaration => declaration.name == declName

/-- Keep only declarations that correspond to a source declaration range, excluding generated
constructors, extensionality lemmas, injectivity theorems, and similar compiler-generated names. -/
def Snapshot.sourceDeclarations (snapshot : Snapshot) : Array ProjectDeclaration :=
  snapshot.declarations.filter fun declaration => declaration.sourceDeclared

/-- Return the compiled type of a declaration when it exists in the environment. -/
def Snapshot.declarationType? (snapshot : Snapshot) (declName : Name) : Option Expr :=
  (snapshot.env.find? declName).map fun info => info.type

/-- Check a canonical declaration owner without depending on source spelling such as `theorem`,
`lemma`, or `noncomputable def`. -/
def checkOwner (snapshot : Snapshot) (declName expectedModule : Name) : Array String :=
  match snapshot.findDeclaration? declName with
  | none => #[s!"missing compiled declaration `{declName}`"]
  | some declaration =>
      if declaration.moduleName == expectedModule then
        #[]
      else
        #[s!"`{declName}` must be owned by `{expectedModule}`, found `{declaration.moduleName}`"]

/-- Check path/namespace ownership semantically: source declarations under a declaration-name prefix
must be owned by modules under the corresponding module prefix. -/
def checkDeclarationPrefixOwner
    (snapshot : Snapshot) (declarationPrefix modulePrefix : Name) : Array String := Id.run do
  let mut errors : Array String := #[]
  for declaration in snapshot.sourceDeclarations do
    if nameMatchesPrefix declaration.name declarationPrefix &&
        !nameMatchesPrefix declaration.moduleName modulePrefix then
      errors := errors.push
        s!"source declaration `{declaration.name}` is owned by `{declaration.moduleName}`, expected module prefix `{modulePrefix}`"
  return errors

/-- Does an expression mention a constant owned by a module under `modulePrefix`? This is intended
for public type/signature dependency checks; direct source-import topology remains a Python concern. -/
def exprUsesModulePrefix (snapshot : Snapshot) (expr : Expr) (modulePrefix : Name) : Bool :=
  expr.getUsedConstants.any fun constName =>
    match declarationModule? snapshot.env constName with
    | some moduleName => nameMatchesPrefix moduleName modulePrefix
    | none => false

/-- Check that a declaration's public compiled type does not depend on any forbidden module layer. -/
def checkTypeDoesNotDependOn
    (snapshot : Snapshot) (declName : Name) (forbiddenModulePrefixes : Array Name) : Array String :=
  match snapshot.declarationType? declName with
  | none => #[s!"missing compiled declaration `{declName}`"]
  | some type => Id.run do
      let mut errors : Array String := #[]
      for forbiddenPrefix in forbiddenModulePrefixes do
        if exprUsesModulePrefix snapshot type forbiddenPrefix then
          errors := errors.push
            s!"type of `{declName}` depends on forbidden module prefix `{forbiddenPrefix}`"
      return errors

/-- Basic harness health check. It intentionally asserts no domain architecture beyond the ability
to enumerate project declarations and distinguish source-declared entries. -/
def checkSnapshotHealth (snapshot : Snapshot) : Array String := Id.run do
  let mut errors : Array String := #[]
  if snapshot.declarations.isEmpty then
    errors := errors.push "compiled project snapshot contains no LeanCondensedMatter declarations"
  if snapshot.sourceDeclarations.isEmpty then
    errors := errors.push "compiled project snapshot contains no source-declared LeanCondensedMatter declarations"
  return errors

/-- A single canonical owner sentinel exercises declaration-to-module resolution in CI. Broader
owner migration is tracked by #1584 L2. -/
def checkSentinelOwner (snapshot : Snapshot) : Array String :=
  checkOwner snapshot `QuantumTheory.DensityOperator
    `LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-- Run all checks against one snapshot and retain every violation. -/
def runChecks (snapshot : Snapshot) (checks : Array NamedCheck) : Array String := Id.run do
  let mut errors : Array String := #[]
  for check in checks do
    for error in check.run snapshot do
      errors := errors.push s!"{check.name}: {error}"
  return errors

/-- Emit all accumulated diagnostics and fail the Lean process only after every registered check
has run. -/
def finishAudit (snapshot : Snapshot) (errors : Array String) : CommandElabM Unit := do
  if errors.isEmpty then
    logInfo m!"Compiled architecture audit passed ({snapshot.declarations.size} project declarations, {snapshot.sourceDeclarations.size} source-declared)."
  else
    for error in errors do
      logError m!"{error}"
    throwError "compiled architecture audit failed with {errors.size} violation(s)"

private def checks : Array NamedCheck := #[
  { name := "snapshot health", run := checkSnapshotHealth },
  { name := "canonical owner sentinel", run := checkSentinelOwner },
]

run_cmd do
  let snapshot ← collectSnapshot
  finishAudit snapshot (runChecks snapshot checks)

end LeanCondensedMatter.ArchitectureAudit
