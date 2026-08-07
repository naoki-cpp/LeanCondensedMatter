import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeTwoPointCoefficient
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.QuadraticParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.NormalizedTwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion

set_option linter.style.header false

/-!
# Bosonic thermal theory

Public umbrella for the convergence-aware free bosonic thermal layer:

- one- and multi-mode Boltzmann weights;
- partition-series and particle-number-weighted summability, including quadratic occupation moments;
- free two-point basis coefficients;
- the uncutoff bosonic two-point specialization of the Common Bloch–de Dominicis framework;
- a normalized free Gibbs functional on an explicit summable-operator submodule;
- the normalized annihilation/creation two-point identity with explicit product admissibility;
- an analytic adapter from bosonic domain/KMS hypotheses to the Common pairing recursion;
- concrete free thermal field labels, pair kernel, and the inherited Wick pairing expansion.

The functional interface does not claim that arbitrary algebraic-Fock endomorphisms are summable or
bounded.  Interacting Dyson/Wick expansions still require explicit product-closure and
operator-integration hypotheses at each order.
-/
