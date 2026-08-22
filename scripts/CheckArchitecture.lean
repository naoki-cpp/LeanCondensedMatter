import Lean
import LeanCondensedMatter
import LeanCondensedMatter.QuantumTheory.POVM.Born
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
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

/-- One compiled module-to-declaration-namespace requirement. -/
structure NamespaceRequirement where
  id : String
  modulePrefix : Name
  declarationPrefix : Name

/-- One layer vertex from the shared declarative architecture graph. -/
structure ArchitectureLayerSpec where
  id : String
  modulePrefixes : Array String
  namespacePrefixes : Array String
  forbiddenNameFragments : Array String
deriving FromJson

/-- One upstream-to-downstream edge from the shared declarative architecture graph. -/
structure ArchitectureEdgeSpec where
  upstream : String
  downstream : String
deriving FromJson

/-- One intentional declaration namespace exception in the shared architecture graph. -/
structure NamespaceExceptionSpec where
  modulePrefix : String
  declarationPrefix : String
deriving FromJson

/-- Shared architecture data. Python consumes the DAG; Lean consumes compiled namespace contracts. -/
structure ArchitectureGraphSpec where
  layers : Array ArchitectureLayerSpec
  edges : Array ArchitectureEdgeSpec
  namespaceExceptions : Array NamespaceExceptionSpec
deriving FromJson

/-- Module-boundary-aware prefix matching for strings representing Lean names. -/
def stringMatchesPrefix (value expectedPrefix : String) : Bool :=
  value == expectedPrefix || value.startsWith (expectedPrefix ++ ".")

/-- Module-boundary-aware prefix matching for Lean names. -/
def nameMatchesPrefix (name expectedPrefix : Name) : Bool :=
  stringMatchesPrefix name.toString expectedPrefix.toString

/-- Normalize a compiled declaration name back to the user-facing source name. -/
def userDeclarationName (name : Name) : Name :=
  privateToUserName name.eraseMacroScopes

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

/-- Find the architecture layer owning a compiled module. -/
def ArchitectureGraphSpec.layerForModule?
    (graph : ArchitectureGraphSpec) (moduleName : Name) : Option ArchitectureLayerSpec :=
  graph.layers.find? fun layer =>
    layer.modulePrefixes.any fun modulePrefix =>
      stringMatchesPrefix moduleName.toString modulePrefix

/-- Whether a declaration is one of the small intentional cross-namespace exceptions. -/
def ArchitectureGraphSpec.isNamespaceException
    (graph : ArchitectureGraphSpec) (moduleName declarationName : Name) : Bool :=
  let moduleString := moduleName.toString
  let declarationString := (userDeclarationName declarationName).toString
  graph.namespaceExceptions.any fun exception =>
    stringMatchesPrefix moduleString exception.modulePrefix &&
      stringMatchesPrefix declarationString exception.declarationPrefix

/-- Load the architecture graph shared with the Python pre-build audit. -/
def loadArchitectureGraph : CommandElabM ArchitectureGraphSpec := do
  let contents ← liftIO <| IO.FS.readFile "scripts/architecture/second_quantization.json"
  let json ← match Json.parse contents with
    | .ok json => pure json
    | .error error => throwError "failed to parse architecture graph JSON: {error}"
  match (fromJson? json : Except String ArchitectureGraphSpec) with
  | .ok graph => pure graph
  | .error error => throwError "failed to decode architecture graph JSON: {error}"

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
    if nameMatchesPrefix (userDeclarationName declaration.name) declarationPrefix &&
        !nameMatchesPrefix declaration.moduleName modulePrefix then
      errors := errors.push
        s!"source declaration `{userDeclarationName declaration.name}` is owned by `{declaration.moduleName}`, expected module prefix `{modulePrefix}`"
  return errors

/-- Enforce module-to-namespace contracts from the shared architecture graph on compiled source
declarations. Private declarations are checked using their original user-facing names. -/
def checkArchitectureGraphNamespaces
    (graph : ArchitectureGraphSpec) (snapshot : Snapshot) : Array String := Id.run do
  let mut errors : Array String := #[]
  for declaration in snapshot.sourceDeclarations do
    let some layer := graph.layerForModule? declaration.moduleName | continue
    if layer.namespacePrefixes.isEmpty then continue
    let userName := userDeclarationName declaration.name
    let userNameString := userName.toString
    let namespaceOk := layer.namespacePrefixes.any fun namespacePrefix =>
      stringMatchesPrefix userNameString namespacePrefix
    let exceptionOk := graph.isNamespaceException declaration.moduleName declaration.name
    if !namespaceOk && !exceptionOk then
      errors := errors.push
        s!"source declaration `{userName}` in module `{declaration.moduleName}` violates namespace contract for layer `{layer.id}`"
    for fragment in layer.forbiddenNameFragments do
      if userNameString.contains fragment then
        errors := errors.push
          s!"source declaration `{userName}` in layer `{layer.id}` contains forbidden name fragment `{fragment}`"
  return errors

/-- Enforce finer path-owned namespace boundaries from compiled declaration metadata. -/
def checkNamespaceRequirements
    (snapshot : Snapshot) (requirements : Array NamespaceRequirement) : Array String := Id.run do
  let mut errors : Array String := #[]
  for declaration in snapshot.sourceDeclarations do
    for requirement in requirements do
      if nameMatchesPrefix declaration.moduleName requirement.modulePrefix then
        let userName := userDeclarationName declaration.name
        unless nameMatchesPrefix userName requirement.declarationPrefix do
          errors := errors.push
            s!"namespace contract `{requirement.id}`: source declaration `{userName}` in module `{declaration.moduleName}` must be under `{requirement.declarationPrefix}`"
  return errors

/-- Does an expression mention a constant owned by a module under `modulePrefix`? This is intended
for public type/signature dependency checks; direct source-import topology remains a Python concern. -/
def exprUsesModulePrefix (snapshot : Snapshot) (expr : Expr) (modulePrefix : Name) : Bool :=
  expr.getUsedConstants.any fun constName =>
    match declarationModule? snapshot.env constName with
    | some moduleName => nameMatchesPrefix moduleName modulePrefix
    | none => false

/-- Does an expression mention one exact compiled constant? -/
def exprUsesConstant (expr : Expr) (expected : Name) : Bool :=
  expr.getUsedConstants.any fun constName => constName == expected

/-- Check that a declaration's compiled type does not depend on any forbidden module layer. -/
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

/-- Check that a declaration's compiled type mentions all required semantic constants. -/
def checkTypeUsesConstants
    (snapshot : Snapshot) (declName : Name) (requiredConstants : Array Name) : Array String :=
  match snapshot.declarationType? declName with
  | none => #[s!"missing compiled declaration `{declName}`"]
  | some type => Id.run do
      let mut errors : Array String := #[]
      for required in requiredConstants do
        unless exprUsesConstant type required do
          errors := errors.push s!"type of `{declName}` must mention semantic API `{required}`"
      return errors

/-- Check all source declaration types in selected modules for exact forbidden constants. This
captures public/private semantic signatures while deliberately ignoring proof-body implementation. -/
def checkModuleDeclarationTypesDoNotUseConstants
    (snapshot : Snapshot) (modulePrefixes forbiddenConstants : Array Name) : Array String := Id.run do
  let mut errors : Array String := #[]
  for declaration in snapshot.sourceDeclarations do
    unless modulePrefixes.any fun prefix => nameMatchesPrefix declaration.moduleName prefix do continue
    let some type := snapshot.declarationType? declaration.name | continue
    for forbidden in forbiddenConstants do
      if exprUsesConstant type forbidden then
        errors := errors.push
          s!"type of `{userDeclarationName declaration.name}` in `{declaration.moduleName}` uses forbidden semantic dependency `{forbidden}`"
  return errors

/-- Check all source declaration types in selected modules for dependencies on forbidden project
layers. Proof-body use is intentionally outside this architecture contract. -/
def checkModuleDeclarationTypesDoNotDependOn
    (snapshot : Snapshot) (modulePrefixes forbiddenModulePrefixes : Array Name) : Array String := Id.run do
  let mut errors : Array String := #[]
  for declaration in snapshot.sourceDeclarations do
    unless modulePrefixes.any fun prefix => nameMatchesPrefix declaration.moduleName prefix do continue
    let some type := snapshot.declarationType? declaration.name | continue
    for forbidden in forbiddenModulePrefixes do
      if exprUsesModulePrefix snapshot type forbidden then
        errors := errors.push
          s!"type of `{userDeclarationName declaration.name}` in `{declaration.moduleName}` depends on forbidden module prefix `{forbidden}`"
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

private def diagonalOwnerRequirements : Array OwnerRequirement :=
  let formulaModule := `LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
  let bridgeModule := `LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation
  #[
    { declaration := `QuantumTheory.DensityOperator.sqrtOp, moduleName := bridgeModule },
    { declaration := `QuantumTheory.DensityOperator.sqrtOp_isHilbertSchmidt, moduleName := bridgeModule },
    { declaration := `QuantumTheory.DensityOperator.expectation_eq_innerHS, moduleName := bridgeModule },
    { declaration := `QuantumTheory.DensityOperator.hasSum_expectation_diagonal, moduleName := formulaModule },
    { declaration := `QuantumTheory.DensityOperator.summable_expectation_diagonal, moduleName := formulaModule },
    { declaration := `QuantumTheory.DensityOperator.expectation_eq_tsum_diagonal, moduleName := formulaModule },
    { declaration := `QuantumTheory.DensityOperator.observableExpectation_eq_tsum_diagonal, moduleName := formulaModule },
    { declaration := `QuantumTheory.DensityOperator.hasSum_diagonal_weights, moduleName := formulaModule },
    { declaration := `QuantumTheory.DensityOperator.summable_diagonal_weights, moduleName := formulaModule },
    { declaration := `QuantumTheory.DensityOperator.diagonal_weight_le_one, moduleName := formulaModule },
    { declaration := `QuantumTheory.normalizedDiagonalWeight, moduleName := formulaModule },
    { declaration := `QuantumTheory.summable_norm_normalizedDiagonalWeight, moduleName := formulaModule },
    { declaration := `QuantumTheory.diagonalDensityOperator_apply_basis, moduleName := formulaModule },
    { declaration := `QuantumTheory.normalizedDiagonalWeight_nonneg, moduleName := formulaModule },
    { declaration := `QuantumTheory.hasSum_normalizedDiagonalWeight, moduleName := formulaModule },
    { declaration := `QuantumTheory.normalizedDiagonalWeight_le_one, moduleName := formulaModule },
  ]

private def quantumCoreOwnerRequirements : Array OwnerRequirement :=
  let postulatesModule := `LeanCondensedMatter.QuantumTheory.Postulates
  let observableExpectationModule :=
    `LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
  let bornModule := `LeanCondensedMatter.QuantumTheory.POVM.Born
  #[
    {
      declaration := `QuantumTheory.POVM
      moduleName := `LeanCondensedMatter.QuantumTheory.POVM.Basic
    },
    { declaration := `QuantumTheory.observableExpValue, moduleName := postulatesModule },
    {
      declaration := `QuantumTheory.DensityOperator.observableExpectation
      moduleName := observableExpectationModule
    },
    { declaration := `QuantumTheory.probNNReal, moduleName := bornModule },
    { declaration := `QuantumTheory.bornPMF, moduleName := bornModule },
    {
      declaration := `QuantumTheory.energyExpValue_eq_tsum_common_eigenbasis
      moduleName := `LeanCondensedMatter.QuantumTheory.Gibbs.DiagonalEnergy
    },
  ]

private def semanticOwnerRequirements : Array OwnerRequirement :=
  let postulatesModule := `LeanCondensedMatter.QuantumTheory.Postulates
  let observableExpectationModule :=
    `LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
  let bornModule := `LeanCondensedMatter.QuantumTheory.POVM.Born
  let purePointDynamicsModule :=
    `LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointDynamics
  let gibbsPurePointModule := `LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint
  let finiteGibbsModule :=
    `LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
  let freeEntropyModule :=
    `LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
  let recursionModule :=
    `LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
  #[
    { declaration := `QuantumTheory.expValueSelfAdjoint, moduleName := postulatesModule },
    { declaration := `QuantumTheory.coe_observableExpValue, moduleName := postulatesModule },
    {
      declaration := `QuantumTheory.DensityOperator.observableExpectationSelfAdjoint
      moduleName := observableExpectationModule
    },
    {
      declaration := `QuantumTheory.DensityOperator.expectation_observable
      moduleName := observableExpectationModule
    },
    {
      declaration := `QuantumTheory.DensityOperator.observableExpectation_pure
      moduleName := observableExpectationModule
    },
    { declaration := `QuantumTheory.probSelfAdjoint, moduleName := bornModule },
    {
      declaration := `QuantumTheory.DensityOperator.expectation_effect_eq_probNNReal
      moduleName := bornModule
    },
    { declaration := `QuantumTheory.hasSum_probNNReal, moduleName := bornModule },
    { declaration := `QuantumTheory.bornPMF_apply, moduleName := bornModule },
    {
      declaration := `QuantumTheory.LinearResponse.purePointDensityOperator
      moduleName := purePointDynamicsModule
    },
    {
      declaration := `QuantumTheory.LinearResponse.purePointDensityOperator_apply_basis
      moduleName := purePointDynamicsModule
    },
    {
      declaration := `QuantumTheory.LinearResponse.purePointNormalizedExpectation
      moduleName := purePointDynamicsModule
    },
    {
      declaration := `QuantumTheory.LinearResponse.purePointNormalizedExpectation_apply
      moduleName := purePointDynamicsModule
    },
    {
      declaration := `QuantumTheory.LinearResponse.isStationary_purePointNormalizedExpectation
      moduleName := purePointDynamicsModule
    },
    { declaration := `QuantumTheory.purePointGibbsDensityOperator, moduleName := gibbsPurePointModule },
    { declaration := `QuantumTheory.finitePurePointGibbsDensityOperator, moduleName := gibbsPurePointModule },
    { declaration := `SecondQuantization.Common.finiteGibbsExpectationLinearMap, moduleName := finiteGibbsModule },
    { declaration := `SecondQuantization.Common.finiteGibbsExpectation, moduleName := finiteGibbsModule },
    { declaration := `SecondQuantization.Common.finiteGibbsExpectation_eq_sum, moduleName := finiteGibbsModule },
    {
      declaration := `SecondQuantization.Fermionic.vonNeumannEntropy_freeGibbsDensityOperator_toReal_eq_sum_configuration
      moduleName := freeEntropyModule
    },
    {
      declaration := `SecondQuantization.Common.BlochDeDominicis.ExpectationPairingRecursion
      moduleName := recursionModule
    },
    {
      declaration := `SecondQuantization.Common.BlochDeDominicis.ExpectationPairingRecursion.expectation_eq_sum_pairing
      moduleName := recursionModule
    },
  ]

private def namespaceRequirements : Array NamespaceRequirement := #[
  {
    id := "single-particle continuum"
    modulePrefix := `LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum
    declarationPrefix := `QuantumMechanics.SingleParticle.Continuum
  },
  {
    id := "fermionic algebraic Fock"
    modulePrefix := `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock
    declarationPrefix := `SecondQuantization.Fermionic.AlgebraicFock
  },
  {
    id := "fermionic lattice"
    modulePrefix := `LeanCondensedMatter.SecondQuantization.Fermionic.Lattice
    declarationPrefix := `SecondQuantization.Fermionic.Lattice
  },
  {
    id := "fermionic transport"
    modulePrefix := `LeanCondensedMatter.SecondQuantization.Fermionic.Transport
    declarationPrefix := `SecondQuantization.Fermionic.Transport
  },
  {
    id := "fermionic validation"
    modulePrefix := `LeanCondensedMatter.SecondQuantization.Fermionic.Validation
    declarationPrefix := `SecondQuantization.Fermionic.Validation
  },
]

private def boundedDimensionIndependentModules : Array Name := #[
  `LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics,
  `LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence,
  `LeanCondensedMatter.Analysis.Operator.TraceClass.Unitary,
  `LeanCondensedMatter.QuantumTheory.LinearResponse.EquationsOfMotion,
  `LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws,
  `LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics,
  `LeanCondensedMatter.QuantumTheory.LinearResponse.DensityExpectation,
  `LeanCondensedMatter.QuantumTheory.DensityOperator.Basic,
  `LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation,
  `LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula,
]

private def modeFoundationModules : Array Name := #[
  `LeanCondensedMatter.SecondQuantization.Common.Algebra.OneParticleSpace,
  `LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis,
  `LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock,
  `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Occupation,
  `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FockSpace,
  `LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.Occupation,
  `LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FockSpace,
]

private def checkTypedSemanticContracts (snapshot : Snapshot) : Array String := Id.run do
  let mut errors : Array String := #[]
  let append (newErrors : Array String) :=
    for error in newErrors do errors := errors.push error

  append <| checkTypeUsesConstants snapshot `QuantumTheory.coe_observableExpValue #[
    `QuantumTheory.observableExpValue, `QuantumTheory.expValue]
  append <| checkTypeUsesConstants snapshot `QuantumTheory.DensityOperator.expectation_observable #[
    `QuantumTheory.DensityOperator.expectation,
    `QuantumTheory.DensityOperator.observableExpectation]
  append <| checkTypeUsesConstants snapshot
    `QuantumTheory.DensityOperator.expectation_effect_eq_probNNReal #[
      `QuantumTheory.DensityOperator.expectation, `QuantumTheory.probNNReal]
  append <| checkTypeUsesConstants snapshot `QuantumTheory.bornPMF_apply #[
    `QuantumTheory.bornPMF, `QuantumTheory.probNNReal]
  append <| checkTypeUsesConstants snapshot
    `QuantumTheory.LinearResponse.BoundedFreeSystem.hamiltonian #[`QuantumTheory.Observable]

  append <| checkModuleDeclarationTypesDoNotUseConstants snapshot
    boundedDimensionIndependentModules #[`FiniteDimensional, `Fintype]
  append <| checkModuleDeclarationTypesDoNotUseConstants snapshot
    #[`LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws] #[`HasDerivAt]
  append <| checkModuleDeclarationTypesDoNotDependOn snapshot
    #[`LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation] #[
      `LeanCondensedMatter.Analysis.Dyson,
      `LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics]
  append <| checkModuleDeclarationTypesDoNotDependOn snapshot
    #[`LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula] #[
      `LeanCondensedMatter.QuantumTheory.Entropy]

  append <| checkModuleDeclarationTypesDoNotUseConstants snapshot
    modeFoundationModules #[`Fintype, `Finite]
  append <| checkModuleDeclarationTypesDoNotUseConstants snapshot
    #[`LeanCondensedMatter.SecondQuantization.Common.Algebra.OneParticleSpace] #[`DecidableEq]
  append <| checkModuleDeclarationTypesDoNotUseConstants snapshot
    #[`LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock] #[
      `Fintype, `FiniteDimensional]
  append <| checkModuleDeclarationTypesDoNotDependOn snapshot
    #[`LeanCondensedMatter.SecondQuantization.Fermionic.Lattice] #[
      `LeanCondensedMatter.QuantumTheory.LinearResponse,
      `LeanCondensedMatter.Transport]
  append <| checkModuleDeclarationTypesDoNotUseConstants snapshot
    #[`LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion]
    #[`Fintype]
  append <| checkModuleDeclarationTypesDoNotDependOn snapshot
    #[`LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion] #[
      `LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator,
      `LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperatorAlgebra,
      `LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge,
      `LeanCondensedMatter.QuantumTheory.DensityOperator]
  append <| checkModuleDeclarationTypesDoNotDependOn snapshot
    #[`LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator] #[
      `LeanCondensedMatter.QuantumTheory.Gibbs,
      `LeanCondensedMatter.QuantumTheory.DensityOperator]

  return errors

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
  {
    name := "diagonal-state owners"
    run := fun snapshot => checkOwnerRequirements snapshot diagonalOwnerRequirements
  },
  {
    name := "quantum core owners"
    run := fun snapshot => checkOwnerRequirements snapshot quantumCoreOwnerRequirements
  },
  {
    name := "semantic endpoint owners"
    run := fun snapshot => checkOwnerRequirements snapshot semanticOwnerRequirements
  },
  {
    name := "path-owned namespaces"
    run := fun snapshot => checkNamespaceRequirements snapshot namespaceRequirements
  },
  { name := "typed semantic contracts", run := checkTypedSemanticContracts },
]

run_cmd do
  let graph ← loadArchitectureGraph
  let snapshot ← collectSnapshot
  let allChecks := checks.push {
    name := "architecture graph namespaces"
    run := fun snapshot => checkArchitectureGraphNamespaces graph snapshot
  }
  finishAudit snapshot (runChecks snapshot allChecks)

end LeanCondensedMatter.ArchitectureAudit
