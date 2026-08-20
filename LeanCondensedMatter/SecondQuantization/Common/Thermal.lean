import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeBoltzmannModeKernel
import LeanCondensedMatter.SecondQuantization.Common.Thermal.DiagonalTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteWeightedTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Statistics-independent thermal states, occupation-basis formulas, and pairing expansions

This umbrella exposes five distinct layers:

- shared one-particle free Boltzmann kernels and generic diagonal trace infrastructure;
- finite Hilbert realization and transport of algebraic Fock operators;
- finite unnormalized and temporary normalized occupation-basis formulas;
- the generic `QuantumTheory.Gibbs.PurePoint` density state with the finite Gibbs expectation adapter;
- the implementation-independent Bloch–de Dominicis expectation recursion and its finite Gibbs
  specialization.

The canonical Gibbs state is the generic pure-point density operator. `SecondQuantization.Common`
adds only the finite Hilbert transport and expectation adapter needed for algebraic Fock operators.
Occupation-basis formulas are proof infrastructure, not a competing normalized-state API. The
Gibbs-specific coordinate comparison is a derived theorem in the finite Gibbs expectation core,
not a separate compatibility layer. The generic pairing recursion has no finite-configuration
assumption; a future bosonic implementation must provide honest summability or domain hypotheses
rather than a false finite occupation basis.
-/
