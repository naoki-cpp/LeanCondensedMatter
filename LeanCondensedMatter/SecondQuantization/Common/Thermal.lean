import LeanCondensedMatter.SecondQuantization.Common.Thermal.DiagonalTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteWeightedTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsOccupationBasisBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis

set_option linter.style.header false

/-!
# Statistics-independent thermal states, occupation-basis formulas, and pairing expansions

Generic diagonal traces, finite weighted occupation-basis sums, their temporary normalized
occupation-basis layer, canonical finite Gibbs density operators and bridges, and the abstract
Bloch–de Dominicis pairing theorem.
-/
