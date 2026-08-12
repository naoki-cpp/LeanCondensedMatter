import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeExchangeCycleSeries

set_option linter.style.header false

/-!
# Free-boson connected-cycle and grand-partition series

The free-boson formal exchange statements are the `ζ = +1` specialization of the shared
statistics-independent free thermal exchange-cycle theorems. The actual convergent bosonic
occupation-space partition sum is handled separately by the bosonic analytic thermal layer.

No formal power series is evaluated at `t = 1` in this file.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- For the shared free Boltzmann kernel, the bosonic connected-cycle series is
`-Σᵢ log(1 - t exp(-β εᵢ))` as a formal power series. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_neg_sum_log
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries 1
        (Common.freeBoltzmannModeKernel ε β) =
      -∑ i : Mode,
        PowerSeries.rescale
          (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  simpa using
    (Common.permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
      (1 : ℂ) (by norm_num) ε β)

/-- The logarithm of the free-boson formal grand-partition series is
`-Σᵢ log(1 - t exp(-β εᵢ))`. -/
theorem logOf_permutationGrandPartitionSeries_freeBoltzmannModeKernel_eq_neg_sum_log
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf
        (Combinatorics.permutationGrandPartitionSeries 1
          (Common.freeBoltzmannModeKernel ε β)) =
      -∑ i : Mode,
        PowerSeries.rescale
          (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  simpa using
    (Common.logOf_permutationGrandPartitionSeries_freeBoltzmannModeKernel_eq_sum_log
      (1 : ℂ) (by norm_num) ε β)

end Bosonic
end SecondQuantization
