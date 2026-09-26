import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreePartitionDeterminant
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeConnectedCycleSeries
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeTwoPointCoefficient
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.QuadraticParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.TotalParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs

set_option linter.style.header false

/-!
# Bosonic thermal theory

The convergence-aware free bosonic thermal layer includes:

- one- and multi-mode Boltzmann weights and the convergent partition sum;
- the finite-mode inverse-determinant interpretation of that partition sum;
- the `ζ = +1` connected-cycle series and formal grand product `∏ᵢ (1 - qᵢ t)⁻¹`;
- particle-number-weighted summability, with arbitrary finite occupation monomials as the canonical
  polynomial owner and quadratic/total-particle-number moments as specializations, plus shifted
  polynomial majorants for ladder-product tails;
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
