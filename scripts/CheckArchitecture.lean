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

/-- One canonical declaration-to-module ownership requirement. -/
structure OwnerRequirement where
  declaration : Name
  moduleName : Name

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

/-- Check a declarative collection of canonical declaration owners. -/
def checkOwnerRequirements
    (snapshot : Snapshot) (requirements : Array OwnerRequirement) : Array String := Id.run do
  let mut errors : Array String := #[]
  for requirement in requirements do
    for error in checkOwner snapshot requirement.declaration requirement.moduleName do
      errors := errors.push error
  return errors

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

private def densityOwnerRequirements : Array OwnerRequirement := #[
  {
    declaration := `QuantumTheory.DensityOperator
    moduleName := `LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
  },
]

private def pureStateDynamicsOwnerRequirements : Array OwnerRequirement :=
  let moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics
  #[
    { declaration := `QuantumTheory.LinearResponse.norm_freePropagator_apply, moduleName },
    { declaration := `QuantumTheory.LinearResponse.phaseState, moduleName },
    { declaration := `QuantumTheory.LinearResponse.evolveState, moduleName },
    { declaration := `QuantumTheory.LinearResponse.evolveState_zero, moduleName },
    { declaration := `QuantumTheory.LinearResponse.evolveState_add, moduleName },
    { declaration := `QuantumTheory.LinearResponse.evolveState_neg_after, moduleName },
    { declaration := `QuantumTheory.LinearResponse.evolveState_after_neg, moduleName },
    { declaration := `QuantumTheory.LinearResponse.evolveState_phaseState, moduleName },
  ]

private def normalizedExpectationOwnerRequirements : Array OwnerRequirement := #[
  {
    declaration := `QuantumTheory.LinearResponse.NormalizedExpectation
    moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation
  },
  {
    declaration := `QuantumTheory.LinearResponse.NormalizedExpectation.pullback
    moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation
  },
  {
    declaration := `QuantumTheory.LinearResponse.NormalizedExpectation.pullback_apply
    moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation
  },
  {
    declaration := `QuantumTheory.LinearResponse.IsStationary
    moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.Stationarity
  },
  {
    declaration := `QuantumTheory.LinearResponse.expectation_heisenbergEvolution_zero
    moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.Stationarity
  },
  {
    declaration := `QuantumTheory.LinearResponse.timeDependentPerturbedObservableMap_one_of_isSelfAdjoint
    moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.UnitaryPerturbation
  },
]

private def pictureEquivalenceOwnerRequirements : Array OwnerRequirement :=
  let pictureModule := `LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence
  let unitaryModule := `LeanCondensedMatter.Analysis.Operator.TraceClass.Unitary
  #[
    { declaration := `QuantumTheory.LinearResponse.heisenbergObservable, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.expValue_evolveState_eq_heisenberg, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.observableExpValue_evolveState_eq_heisenberg, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.evolveDensityOperator, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.evolveDensityOperator_isPositive, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.evolveDensityOperator_trace_eq_one, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.freePropagatorLinearIsometryEquiv, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.evolveHilbertBasis, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.expectation_evolveDensityOperator_eq_heisenberg, moduleName := pictureModule },
    { declaration := `QuantumTheory.LinearResponse.observableExpectation_evolveDensityOperator_eq_heisenberg, moduleName := pictureModule },
    { declaration := `ContinuousLinearMap.unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.eigenspace_unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.finrank_eigenspace_unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.hasSummableRealEigenvalues_unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.spectralTrace_unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.isCompactOperator_unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.IsPositive.unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.SpectralTraceClass.unitaryConjugate, moduleName := unitaryModule },
    { declaration := `ContinuousLinearMap.SpectralTraceClass.trace_unitaryConjugate, moduleName := unitaryModule },
    {
      declaration := `QuantumTheory.DensityOperator.exists_diagonal_hilbertBasis
      moduleName := `LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
    },
  ]

private def equationsOfMotionOwnerRequirements : Array OwnerRequirement :=
  let moduleName := `LeanCondensedMatter.QuantumTheory.LinearResponse.EquationsOfMotion
  #[
    { declaration := `QuantumTheory.LinearResponse.hasDerivAt_freePropagator, moduleName },
    { declaration := `QuantumTheory.LinearResponse.hasDerivAt_freePropagator_neg, moduleName },
    { declaration := `QuantumTheory.LinearResponse.schrodingerGenerator_commute_freePropagator, moduleName },
    { declaration := `QuantumTheory.LinearResponse.schrodingerEquation, moduleName },
    { declaration := `QuantumTheory.LinearResponse.heisenbergEquation, moduleName },
    { declaration := `QuantumTheory.LinearResponse.vonNeumannEquation, moduleName },
  ]

private def conservationOwnerRequirements : Array OwnerRequirement :=
  let conservationModule := `LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws
  let densityExpectationModule := `LeanCondensedMatter.QuantumTheory.LinearResponse.DensityExpectation
  #[
    { declaration := `QuantumTheory.LinearResponse.commute_freePropagator_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.heisenbergEvolution_eq_self_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.heisenbergObservable_eq_self_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.expValue_evolveState_eq_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.observableExpValue_evolveState_eq_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.expectation_evolveDensityOperator_eq_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.observableExpectation_evolveDensityOperator_eq_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.expValue_hamiltonian_evolveState, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.observableExpValue_hamiltonian_evolveState, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.expectation_hamiltonian_evolveDensityOperator, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.observableExpectation_hamiltonian_evolveDensityOperator, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.unitaryConjugate_freePropagator_eq_self_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.evolveDensityOperator_eq_self_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.LinearResponse.isStationary_toNormalizedExpectation_of_commute_hamiltonian, moduleName := conservationModule },
    { declaration := `QuantumTheory.DensityOperator.toNormalizedExpectation, moduleName := densityExpectationModule },
    { declaration := `QuantumTheory.DensityOperator.toNormalizedExpectation_apply, moduleName := densityExpectationModule },
    {
      declaration := `QuantumTheory.DensityOperator.ext
      moduleName := `LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
    },
  ]

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
  {
    name := "density canonical owners"
    run := fun snapshot => checkOwnerRequirements snapshot densityOwnerRequirements
  },
  {
    name := "pure-state dynamics owners"
    run := fun snapshot => checkOwnerRequirements snapshot pureStateDynamicsOwnerRequirements
  },
  {
    name := "normalized-expectation owners"
    run := fun snapshot => checkOwnerRequirements snapshot normalizedExpectationOwnerRequirements
  },
  {
    name := "picture-equivalence owners"
    run := fun snapshot => checkOwnerRequirements snapshot pictureEquivalenceOwnerRequirements
  },
  {
    name := "equations-of-motion owners"
    run := fun snapshot => checkOwnerRequirements snapshot equationsOfMotionOwnerRequirements
  },
  {
    name := "conservation-law owners"
    run := fun snapshot => checkOwnerRequirements snapshot conservationOwnerRequirements
  },
]

run_cmd do
  let snapshot ← collectSnapshot
  finishAudit snapshot (runChecks snapshot checks)

end LeanCondensedMatter.ArchitectureAudit
