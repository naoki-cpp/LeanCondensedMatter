import Lean
import LeanCondensedMatter
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import Lean.Elab.Command
import Lean.Util.FoldConsts

open Lean Elab Command

namespace LeanCondensedMatter.SemanticBoundaryAudit

structure ProjectDeclaration where
  name : Name
  moduleName : Name
  sourceDeclared : Bool

structure Snapshot where
  env : Environment
  declarations : Array ProjectDeclaration

structure BoundaryRule where
  id : String
  modulePrefixes : Array Name
  forbiddenConstants : Array Name
  forbiddenModulePrefixes : Array Name

def stringMatchesPrefix (value expectedPrefix : String) : Bool :=
  value == expectedPrefix || value.startsWith (expectedPrefix ++ ".")

def nameMatchesPrefix (name expectedPrefix : Name) : Bool :=
  stringMatchesPrefix name.toString expectedPrefix.toString

def userDeclarationName (name : Name) : Name :=
  privateToUserName name.eraseMacroScopes

def isProjectModule (moduleName : Name) : Bool :=
  moduleName.getRoot.toString == "LeanCondensedMatter"

def declarationModule? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx.get? declName
  env.header.moduleNames[moduleIdx]?

def collectSnapshot (modulePrefixes : Array Name) : CommandElabM Snapshot := do
  let env ← getEnv
  let mut declarations : Array ProjectDeclaration := #[]
  for (declName, _) in env.constants.toList do
    let some moduleName := declarationModule? env declName | continue
    unless isProjectModule moduleName do continue
    unless modulePrefixes.any (fun modulePrefix => nameMatchesPrefix moduleName modulePrefix) do
      continue
    let sourceDeclared := (← findDeclarationRanges? declName).isSome
    declarations := declarations.push { name := declName, moduleName, sourceDeclared }
  return { env, declarations }

def Snapshot.sourceDeclarations (snapshot : Snapshot) : Array ProjectDeclaration :=
  snapshot.declarations.filter fun declaration => declaration.sourceDeclared

def Snapshot.declarationType? (snapshot : Snapshot) (declName : Name) : Option Expr :=
  (snapshot.env.find? declName).map fun info => info.type

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

private def boundaryRules : Array BoundaryRule := #[
  {
    id := "bounded dimension independence"
    modulePrefixes := boundedDimensionIndependentModules
    forbiddenConstants := #[`FiniteDimensional, `Fintype]
    forbiddenModulePrefixes := #[]
  },
  {
    id := "linear-response expectation layering"
    modulePrefixes := #[`LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation]
    forbiddenConstants := #[]
    forbiddenModulePrefixes := #[
      `LeanCondensedMatter.Analysis.Dyson,
      `LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics,
    ]
  },
  {
    id := "density diagonal formula layering"
    modulePrefixes := #[`LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula]
    forbiddenConstants := #[]
    forbiddenModulePrefixes := #[`LeanCondensedMatter.QuantumTheory.Entropy]
  },
  {
    id := "mode foundation finiteness independence"
    modulePrefixes := modeFoundationModules
    forbiddenConstants := #[`Fintype, `Finite]
    forbiddenModulePrefixes := #[]
  },
  {
    id := "one-particle space decidable-equality independence"
    modulePrefixes := #[`LeanCondensedMatter.SecondQuantization.Common.Algebra.OneParticleSpace]
    forbiddenConstants := #[`DecidableEq]
    forbiddenModulePrefixes := #[]
  },
  {
    id := "fermionic algebraic-Fock finiteness independence"
    modulePrefixes := #[`LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock]
    forbiddenConstants := #[`Fintype, `FiniteDimensional]
    forbiddenModulePrefixes := #[]
  },
  {
    id := "fermionic lattice layering"
    modulePrefixes := #[`LeanCondensedMatter.SecondQuantization.Fermionic.Lattice]
    forbiddenConstants := #[]
    forbiddenModulePrefixes := #[
      `LeanCondensedMatter.QuantumTheory.LinearResponse,
      `LeanCondensedMatter.Transport,
    ]
  },
  {
    id := "generic expectation recursion"
    modulePrefixes := #[
      `LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion]
    forbiddenConstants := #[`Fintype]
    forbiddenModulePrefixes := #[
      `LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator,
      `LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperatorAlgebra,
      `LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge,
      `LeanCondensedMatter.QuantumTheory.DensityOperator,
    ]
  },
  {
    id := "finite-Hilbert operator layering"
    modulePrefixes := #[`LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator]
    forbiddenConstants := #[]
    forbiddenModulePrefixes := #[
      `LeanCondensedMatter.QuantumTheory.Gibbs,
      `LeanCondensedMatter.QuantumTheory.DensityOperator,
    ]
  },
]

private def watchedModulePrefixes : Array Name :=
  boundaryRules.foldl (fun prefixes rule =>
    rule.modulePrefixes.foldl (fun prefixes modulePrefix =>
      if prefixes.contains modulePrefix then prefixes else prefixes.push modulePrefix) prefixes) #[]

private def ruleMatchesModule (rule : BoundaryRule) (moduleName : Name) : Bool :=
  rule.modulePrefixes.any fun modulePrefix => nameMatchesPrefix moduleName modulePrefix

def checkSemanticBoundaries (snapshot : Snapshot) : Array String := Id.run do
  let mut errors : Array String := #[]
  for declaration in snapshot.sourceDeclarations do
    let matchingRules := boundaryRules.filter fun rule => ruleMatchesModule rule declaration.moduleName
    if matchingRules.isEmpty then continue
    let some type := snapshot.declarationType? declaration.name | continue
    let usedConstants := type.getUsedConstants
    let mut usedModules : Array Name := #[]
    for constName in usedConstants do
      if let some moduleName := declarationModule? snapshot.env constName then
        usedModules := usedModules.push moduleName
    for rule in matchingRules do
      for forbidden in rule.forbiddenConstants do
        if usedConstants.any fun constName => constName == forbidden then
          errors := errors.push
            s!"{rule.id}: type of `{userDeclarationName declaration.name}` in `{declaration.moduleName}` uses forbidden semantic dependency `{forbidden}`"
      for forbiddenPrefix in rule.forbiddenModulePrefixes do
        if usedModules.any fun moduleName => nameMatchesPrefix moduleName forbiddenPrefix then
          errors := errors.push
            s!"{rule.id}: type of `{userDeclarationName declaration.name}` in `{declaration.moduleName}` depends on forbidden module prefix `{forbiddenPrefix}`"
  return errors

run_cmd do
  let snapshot ← collectSnapshot watchedModulePrefixes
  if snapshot.declarations.isEmpty || snapshot.sourceDeclarations.isEmpty then
    throwError "compiled semantic-boundary audit found no watched project declarations"
  let errors := checkSemanticBoundaries snapshot
  if errors.isEmpty then
    logInfo m!"Compiled semantic-boundary audit passed ({snapshot.sourceDeclarations.size} watched source declarations)."
  else
    for error in errors do logError m!"{error}"
    throwError "compiled semantic-boundary audit failed with {errors.size} violation(s)"

end LeanCondensedMatter.SemanticBoundaryAudit
