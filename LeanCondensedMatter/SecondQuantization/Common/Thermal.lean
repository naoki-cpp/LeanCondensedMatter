import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteWeightedTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Statistics-independent thermal states, occupation-basis formulas, and pairing expansions

The statistics-independent thermal theory separates five layers:

- algebraic diagonal-trace and weighted-functional infrastructure;
- finite Hilbert realization and transport of algebraic Fock operators;
- the generic `QuantumTheory.Gibbs.PurePoint` density state with the finite Gibbs expectation adapter;
- finite Gibbs trace-ratio and weighted-coordinate formulas;
- the implementation-independent Bloch–de Dominicis expectation recursion and its finite Gibbs
  pairing specialization.

The canonical Gibbs state is the generic pure-point density operator. `SecondQuantization.Common`
adds only the finite Hilbert transport and expectation adapter needed for algebraic Fock operators.
Occupation-basis formulas are proof infrastructure, not a competing normalized-state API. The
Gibbs-specific coordinate comparison is a derived theorem in `FiniteGibbsCoordinate`, not a
Bloch--de Dominicis implementation detail. The generic pairing recursion has no finite-configuration
assumption; a future bosonic implementation must provide honest summability or domain hypotheses
rather than a false finite occupation basis.
-/
