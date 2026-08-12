import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeExchangeCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-fermion connected-cycle series

This file gives the generic exchange/cumulant backend a concrete free-fermion thermal consumer.
For a finite mode set, the statistics-independent one-particle Boltzmann weights form the shared
diagonal matrix kernel

`Kᵢⱼ = δᵢⱼ exp(-β εᵢ)`.

The arbitrary-`ζ` free thermal exchange-cycle theorem is owned by `Common`; here it is specialized
to fermionic `ζ = -1`. The ordinary finite determinant `det(1 + K)` remains a fermion-specific
physical consumer boundary.

Everything here is finite or formal. In particular, no convergence statement or evaluation of the
formal variable `t` at `1` is asserted.
-/

namespace SecondQuantization
namespace Fermionic

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

/-- For the free diagonal kernel, the fermionic connected-cycle series is the sum of the formal
single-mode logarithms `log(1 + t exp(-β εᵢ))`. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries (-1)
        (Common.freeBoltzmannModeKernel ε β) =
      ∑ i : Mode,
        PowerSeries.rescale (Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  simpa using
    (Common.permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
      (-1 : ℂ) (by norm_num) ε β)

/-- The logarithm of the free-fermion formal grand-partition series is the same sum of modewise
`log(1 + t exp(-β εᵢ))` terms. -/
theorem logOf_permutationGrandPartitionSeries_freeBoltzmannModeKernel_eq_sum_log
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf
        (Combinatorics.permutationGrandPartitionSeries (-1)
          (Common.freeBoltzmannModeKernel ε β)) =
      ∑ i : Mode,
        PowerSeries.rescale (Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  simpa using
    (Common.logOf_permutationGrandPartitionSeries_freeBoltzmannModeKernel_eq_sum_log
      (-1 : ℂ) (by norm_num) ε β)

end Fermionic
end SecondQuantization
