import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# Occupation-basis bridge for finite Gibbs expectations

This module is the explicit boundary between the canonical finite Gibbs density-state expectation
and the temporary normalized weighted occupation-basis formula. Physical Bloch–de Dominicis proofs
should use `finiteGibbsExpectation_eq_trace_div` from `GibbsExpectation.Core`; proofs that need to
unfold finite occupation-basis sums may import this bridge deliberately.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The canonical density-state expectation agrees with the temporary normalized occupation-basis
formula on a finite configuration space. -/
theorem finiteGibbsExpectation_eq_normalizedWeightedDiagonal (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      normalizedWeightedDiagonal (boltzmannWeight energy β) A := by
  rw [finiteGibbsExpectation_eq_trace_div, normalizedWeightedDiagonal,
    traceFock_diagonalEvolution_comp_eq_weightedTrace,
    traceFock_diagonalEvolution_eq_weightSum]

end Common
end SecondQuantization
