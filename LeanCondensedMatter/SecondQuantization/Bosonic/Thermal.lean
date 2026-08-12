import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreePartitionDeterminant
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeConnectedCycleSeries
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeTwoPointCoefficient
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.QuadraticParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.TotalParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.NormalizedTwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteMixedTwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcretePairKernel
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OrderedProductSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OperatorPeel
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeKMSRotation
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreePeelIndexed
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeFirstPair
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteExpectationRecursion

set_option linter.style.header false

/-!
# Bosonic thermal theory

Public umbrella for the convergence-aware free bosonic thermal layer:

- one- and multi-mode Boltzmann weights and the convergent partition sum;
- the finite-mode inverse-determinant interpretation of that partition sum;
- the `ζ = +1` connected-cycle series and formal grand product `∏ᵢ (1 - qᵢ t)⁻¹`;
- particle-number-weighted summability, including arbitrary finite occupation monomials, shifted polynomial majorants, quadratic occupation, and total-particle-number moments;
- free two-point basis coefficients;
- the uncutoff bosonic two-point specialization of the Common Bloch–de Dominicis framework;
- a normalized free Gibbs functional on an explicit summable-operator submodule;
- concrete summability and normalized values for both mixed creation/annihilation contractions;
- same-type zero contractions and the theorem identifying every two-field Gibbs expectation with `freeThermalPairValue`;
- free-Gibbs domain membership for arbitrary fixed-length ordered products of free thermal fields;
- a Common-backed finite CCR operator-peel identity and its position-indexed finite-sum form;
- occupation-reindexed `tsumTrace` cyclicity for single ladder operators and the resulting normalized free-Gibbs KMS rotation;
- the solved bosonic first-pair thermal equation with the bare CCR coefficient identified with `freeThermalPairValue`;
- the concrete multi-point first-pair recurrence and a no-extra-admissibility `ExpectationPairingRecursion` instance;
- concrete free thermal field labels, pair kernel, and the inherited Wick pairing expansion.

The functional interface does not claim that arbitrary algebraic-Fock endomorphisms are summable or
bounded. Interacting Dyson/Wick expansions still require explicit product-closure and
operator-integration hypotheses at each order.
-/
