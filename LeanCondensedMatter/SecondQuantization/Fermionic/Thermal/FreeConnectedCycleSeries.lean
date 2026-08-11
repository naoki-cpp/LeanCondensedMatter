import LeanCondensedMatter.Analysis.PowerSeries.PermutationCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-fermion connected-cycle series

This file gives the generic exchange/cumulant backend a concrete free-fermion thermal consumer.
For a finite mode set, the one-particle Boltzmann weights form a diagonal matrix kernel

`Kᵢⱼ = δᵢⱼ exp(-β εᵢ)`.

The arbitrary-`ζ` diagonal connected-cycle/log decomposition is owned by
`Analysis.PowerSeries.PermutationTraceLog`. Here it is specialized to fermionic `ζ = -1`, while
the ordinary finite determinant `det(1 + K)` is identified with the already-established free
fermion partition function.

Everything here is finite or formal. In particular, no convergence statement or evaluation of the
formal variable `t` at `1` is asserted.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- The diagonal one-particle Boltzmann kernel for a finite free-fermion mode set. -/
noncomputable def freeBoltzmannModeKernel (ε : Mode → ℝ) (β : ℝ) : Matrix Mode Mode ℂ := by
  classical
  exact Matrix.diagonal fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))

private theorem freeBoltzmannModeKernel_eq_diagonal [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    freeBoltzmannModeKernel ε β =
      Matrix.diagonal (fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [freeBoltzmannModeKernel]
  · simp [freeBoltzmannModeKernel, hij]

/-- The finite free-fermion partition function is the determinant of `1 + K`, where `K` is the
diagonal one-particle Boltzmann kernel. Determinant appears only at this physical consumer boundary;
it is not a second exchange-statistics backend. -/
theorem freePartitionFunction_eq_det_one_add_freeBoltzmannModeKernel
    [LinearOrder Mode] [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β =
      Matrix.det (1 + freeBoltzmannModeKernel ε β) := by
  classical
  rw [freePartitionFunction_eq_prod]
  have hdiag :
      (1 + freeBoltzmannModeKernel ε β : Matrix Mode Mode ℂ) =
        Matrix.diagonal (fun i => 1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [freeBoltzmannModeKernel]
    · simp [freeBoltzmannModeKernel, hij]
  rw [hdiag, Matrix.det_diagonal]

/-- For the free diagonal kernel, the fermionic connected-cycle series is the sum of the formal
single-mode logarithms `log(1 + t exp(-β εᵢ))`.

This is the `ζ = -1` specialization of the generic diagonal-kernel theorem; it does not evaluate
the formal series at `t = 1`. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries (-1) (freeBoltzmannModeKernel ε β) =
      ∑ i : Mode,
        PowerSeries.rescale (Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  classical
  rw [freeBoltzmannModeKernel_eq_diagonal]
  simpa using
    (Combinatorics.permutationConnectedCycleSeries_diagonal_eq_neg_inv_smul_sum_log
      (-1 : ℂ) (fun i : Mode => Complex.exp (-(β : ℂ) * (ε i : ℂ))) (by norm_num))

end Fermionic
end SecondQuantization
