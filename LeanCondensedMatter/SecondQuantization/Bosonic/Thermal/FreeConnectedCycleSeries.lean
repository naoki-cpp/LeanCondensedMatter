import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeExchangeCycleSeries

set_option linter.style.header false

/-!
# Free-boson connected-cycle and grand-partition series

The free-boson formal exchange statements are the `ζ = +1` specialization of the shared
statistics-independent free thermal exchange-cycle theorem. The formal grand-partition series is the
finite product `∏ᵢ (1 - qᵢ t)⁻¹`, and its logarithm is obtained from the shared `logOf` product and
inverse algebra.

The actual convergent bosonic occupation-space partition sum is handled separately by the bosonic
analytic thermal layer. No formal power series is evaluated at `t = 1` here.
-/

namespace SecondQuantization
namespace Bosonic

open scoped BigOperators

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

/-- Formal finite-mode free-boson grand-partition series
`𝒵_B(t) = ∏ᵢ (1 - exp(-β εᵢ) t)⁻¹`. -/
noncomputable def freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) : PowerSeries ℂ :=
  ∏ i : Mode,
    (1 + (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) • PowerSeries.X)⁻¹

@[simp]
theorem constantCoeff_freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.constantCoeff (freeGrandPartitionSeries ε β) = 1 := by
  classical
  simp [freeGrandPartitionSeries]

/-- The formal logarithm of the free-boson grand product is
`-Σᵢ log(1 - t exp(-β εᵢ))`. -/
theorem logOf_freeGrandPartitionSeries_eq_neg_sum_log [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeGrandPartitionSeries ε β) =
      -∑ i : Mode,
        PowerSeries.rescale
          (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  classical
  unfold freeGrandPartitionSeries
  calc
    PowerSeries.logOf
        (∏ i : Mode,
          (1 + (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) • PowerSeries.X)⁻¹) =
        ∑ i : Mode,
          PowerSeries.logOf
            ((1 + (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) • PowerSeries.X)⁻¹) := by
      exact PowerSeries.logOf_fintype_prod _ (fun i => by simp)
    _ = ∑ i : Mode,
        -PowerSeries.rescale
          (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
      apply Fintype.sum_congr
      intro i
      rw [PowerSeries.logOf_inv (by simp), PowerSeries.logOf_one_add_smul_X]
    _ = -∑ i : Mode,
        PowerSeries.rescale
          (-Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
      rw [Finset.sum_neg_distrib]

/-- Free-boson formal linked-cluster identity: the logarithm of the finite grand product equals the
`ζ = +1` connected-cycle series. -/
theorem logOf_freeGrandPartitionSeries_eq_permutationConnectedCycleSeries
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeGrandPartitionSeries ε β) =
      Combinatorics.permutationConnectedCycleSeries 1
        (Common.freeBoltzmannModeKernel ε β) := by
  rw [logOf_freeGrandPartitionSeries_eq_neg_sum_log,
    permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_neg_sum_log]

end Bosonic
end SecondQuantization
