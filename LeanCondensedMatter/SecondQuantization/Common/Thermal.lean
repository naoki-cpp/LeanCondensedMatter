import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeBoltzmannModeKernel
import LeanCondensedMatter.SecondQuantization.Common.Thermal.DiagonalTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteWeightedTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsOccupationBasisBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.PurePointCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis

set_option linter.style.header false

/-!
# Statistics-independent thermal states, occupation-basis formulas, and pairing expansions

This umbrella exposes five distinct layers:

- shared one-particle free Boltzmann kernels and generic diagonal trace infrastructure;
- finite unnormalized weighted occupation-basis sums;
- the temporary normalized occupation-basis formula used by explicit finite-sum proofs;
- canonical finite Gibbs density operators and opt-in expectation/occupation-basis bridges;
- the implementation-independent Bloch–de Dominicis expectation recursion and its finite Gibbs
  specialization.

The canonical physical expectation is the density-state expectation. Occupation-basis formulas are
proof infrastructure, not a competing normalized-state API. The generic pairing recursion has no
finite-configuration assumption; a future bosonic implementation must provide honest summability or
domain hypotheses rather than a false finite occupation basis.
-/
