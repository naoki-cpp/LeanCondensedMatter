import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeExchangeCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-fermion connected-cycle and grand-partition series

The free-fermion formal exchange statements are the `ζ = -1` specialization of the shared
statistics-independent free thermal exchange-cycle theorem. The formal grand-partition series is the
finite product `∏ᵢ (1 + qᵢ t)`, and its logarithm is obtained from the shared `logOf` product algebra.

The ordinary finite determinant `det(1 + K)` remains a fermion-specific physical consumer boundary.
No formal power series is evaluated at `t = 1` here.
-/

namespace SecondQuantization
namespace Fermionic

open scoped BigOperators

variable {Mode : Type*}

/-- The finite free-fermion partition function is the determinant of `1 + K`, where `K` is the
shared diagonal one-particle Boltzmann kernel. Determinant appears only at this physical consumer
boundary; it is not a second exchange-statistics backend. -/
theorem freePartitionFunction_eq_det_one_add_freeBoltzmannModeKernel
    [LinearOrder Mode] [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β =
      Matrix.det (1 + Common.freeBoltzmannModeKernel ε β) := by
  classical
  rw [freePartitionFunction_eq_prod]
  have hdiag :
      (1 + Common.freeBoltzmannModeKernel ε β : Matrix Mode Mode ℂ) =
        Matrix.diagonal (fun i => 1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
    rw [Common.freeBoltzmannModeKernel_eq_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag, Matrix.det_diagonal]

/-- For the shared free Boltzmann kernel, the fermionic connected-cycle series is the sum of the
formal single-mode logarithms `log(1 + t exp(-β εᵢ))`. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries (-1)
        (Common.freeBoltzmannModeKernel ε β) =
      ∑ i : Mode,
        PowerSeries.rescale (Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  simpa using
    (Common.permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
      (-1 : ℂ) (by norm_num) ε β)

/-- Formal finite-mode free-fermion grand-partition series
`𝒵_F(t) = ∏ᵢ (1 + exp(-β εᵢ) t)`. -/
noncomputable def freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) : PowerSeries ℂ :=
  ∏ i : Mode,
    (1 + Complex.exp (-(β : ℂ) * (ε i : ℂ)) • PowerSeries.X)

@[simp]
theorem constantCoeff_freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.constantCoeff (freeGrandPartitionSeries ε β) = 1 := by
  classical
  simp [freeGrandPartitionSeries]

/-- The formal logarithm of the free-fermion grand product is the sum of the modewise
`log(1 + t exp(-β εᵢ))` series. -/
theorem logOf_freeGrandPartitionSeries_eq_sum_log [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeGrandPartitionSeries ε β) =
      ∑ i : Mode,
        PowerSeries.rescale (Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  classical
  unfold freeGrandPartitionSeries
  rw [PowerSeries.logOf_fintype_prod _ (fun i => by simp)]
  simp_rw [PowerSeries.logOf_one_add_smul_X]

/-- Free-fermion formal linked-cluster identity: the logarithm of the finite grand product equals the
`ζ = -1` connected-cycle series. -/
theorem logOf_freeGrandPartitionSeries_eq_permutationConnectedCycleSeries
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeGrandPartitionSeries ε β) =
      Combinatorics.permutationConnectedCycleSeries (-1)
        (Common.freeBoltzmannModeKernel ε β) := by
  rw [logOf_freeGrandPartitionSeries_eq_sum_log,
    permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log]

end Fermionic
end SecondQuantization
