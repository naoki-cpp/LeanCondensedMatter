import LeanCondensedMatter.Analysis.PowerSeries.PermutationTraceLog
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-fermion connected-cycle series

This file gives the W3 exchange/cumulant backend a concrete free-fermion thermal consumer.
For a finite mode set, the one-particle Boltzmann weights form a diagonal matrix kernel

`Kᵢⱼ = δᵢⱼ exp(-β εᵢ)`.

The ordinary finite determinant `det(1 + K)` is exactly the already-established free fermion
partition function. On the same kernel, the fermionic (`ζ = -1`) connected-cycle series is the sum
of the modewise formal logarithms `log(1 + t exp(-β εᵢ))`.

Everything here is finite or formal. In particular, no convergence statement or evaluation of the
formal variable `t` at `1` is asserted.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [Fintype Mode]

/-- The diagonal one-particle Boltzmann kernel for a finite free-fermion mode set. -/
noncomputable def freeBoltzmannModeKernel (ε : Mode → ℝ) (β : ℝ) : Matrix Mode Mode ℂ := by
  classical
  exact Matrix.diagonal fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ))

private theorem freeBoltzmannModeKernel_pow [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) (m : ℕ) :
    freeBoltzmannModeKernel ε β ^ m =
      Matrix.diagonal (fun i => Complex.exp (-(β : ℂ) * (ε i : ℂ)) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, freeBoltzmannModeKernel, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [pow_succ]

private theorem trace_freeBoltzmannModeKernel_pow [DecidableEq Mode]
    (ε : Mode → ℝ) (β : ℝ) (m : ℕ) :
    Matrix.trace (freeBoltzmannModeKernel ε β ^ m) =
      ∑ i : Mode, Complex.exp (-(β : ℂ) * (ε i : ℂ)) ^ m := by
  rw [freeBoltzmannModeKernel_pow, Matrix.trace_diagonal]

/-- The finite free-fermion partition function is the determinant of `1 + K`, where `K` is the
diagonal one-particle Boltzmann kernel. Determinant appears only at this physical consumer boundary;
it is not a second exchange-statistics backend. -/
theorem freePartitionFunction_eq_det_one_add_freeBoltzmannModeKernel
    [LinearOrder Mode] (ε : Mode → ℝ) (β : ℝ) :
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

This is a formal-power-series identity; it does not evaluate the series at `t = 1`. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
    (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries (-1) (freeBoltzmannModeKernel ε β) =
      ∑ i : Mode,
        PowerSeries.rescale (Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  classical
  rw [Combinatorics.permutationConnectedCycleSeries_neg_one_eq_traceLog]
  ext m
  rw [Combinatorics.coeff_formalTraceLogOneSubSeries]
  simp only [neg_neg, one_pow, one_mul]
  rw [trace_freeBoltzmannModeKernel_pow]
  simp only [map_sum, PowerSeries.coeff_rescale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Fermionic
end SecondQuantization
