import LeanCondensedMatter.Permutation.ConnectedCycleSeries
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Formal trace-log interpretation of connected permutation cycles

This file completes the formal-log layer of W3 without constructing a power series over the
noncommutative matrix algebra. Mathlib's scalar `PowerSeries.log` and `PowerSeries.rescale` remain
the sole logarithm and scalar-substitution implementations. The rescaled scalar logarithm is then
paired coefficientwise with the matrix power trace `tr(K^m)`.

The resulting scalar series is the coefficientwise meaning of `tr log(1 - ζ t K)`. The canonical
identity is division-free: multiplying the connected-cycle series by `ζ` gives the negative
trace-log series for every exchange weight, including `ζ = 0`. Division by `ζ` appears only in
nonzero-weight specializations.
-/

namespace Combinatorics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Apply scalar power-series coefficients to the power traces of a finite matrix.

This is coefficientwise rather than an algebra homomorphism: it deliberately does not pretend that
`Matrix ι ι ℂ` is a commutative coefficient ring. -/
private noncomputable def tracePowerTransform
    (K : Matrix ι ι ℂ) (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => PowerSeries.coeff m f * Matrix.trace (K ^ m)

private theorem coeff_tracePowerTransform
    (K : Matrix ι ι ℂ) (f : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (tracePowerTransform K f) =
      PowerSeries.coeff m f * Matrix.trace (K ^ m) :=
  PowerSeries.coeff_mk m _

/-- The formal scalar series representing `tr log(1 - ζ t K)` through matrix power traces.

`PowerSeries.rescale (-ζ)` is Mathlib's substitution `f(X) ↦ f(-ζ X)`, so this definition uses
Mathlib's `log(1 + X)` directly rather than reimplementing logarithm coefficients. -/
noncomputable def formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) : PowerSeries ℂ :=
  tracePowerTransform K (PowerSeries.rescale (-ζ) (PowerSeries.log ℂ))

@[simp]
theorem coeff_formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) :
    PowerSeries.coeff m (formalTraceLogOneSubSeries ζ K) =
      (-ζ) ^ m * PowerSeries.coeff m (PowerSeries.log ℂ) * Matrix.trace (K ^ m) := by
  simp [formalTraceLogOneSubSeries, coeff_tracePowerTransform]

@[simp]
theorem constantCoeff_formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    PowerSeries.constantCoeff (formalTraceLogOneSubSeries ζ K) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

private theorem coeff_log_complex_of_pos (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m (PowerSeries.log ℂ) =
      (-1 : ℂ) ^ (m + 1) / (m : ℂ) := by
  rw [PowerSeries.coeff_log, ite_eq_right (Nat.ne_of_gt hm)]
  change (((-1 : ℚ) ^ (m + 1) / (m : ℚ) : ℚ) : ℂ) =
    (-1 : ℂ) ^ (m + 1) / (m : ℂ)
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]

private theorem neg_pow_mul_neg_one_pow_succ (ζ : ℂ) (m : ℕ) :
    (-ζ) ^ m * (-1 : ℂ) ^ (m + 1) = -ζ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ (-ζ), pow_succ (-1 : ℂ) (m + 1)]
      calc
        (-ζ) ^ m * -ζ * ((-1 : ℂ) ^ (m + 1) * -1) =
            ((-ζ) ^ m * (-1 : ℂ) ^ (m + 1)) * ((-ζ) * -1) := by ring
        _ = (-ζ ^ m) * ζ := by rw [ih]; ring
        _ = -ζ ^ (m + 1) := by rw [pow_succ]; ring

/-- Division-free formal trace-log identity for arbitrary exchange weight.

Multiplying the connected-cycle series by `ζ` gives the negative coefficientwise trace-log
series, including at the `ζ = 0` boundary. -/
theorem smul_permutationConnectedCycleSeries_eq_neg_traceLog
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    ζ • permutationConnectedCycleSeries ζ K =
      -formalTraceLogOneSubSeries ζ K := by
  ext m
  rw [PowerSeries.coeff_smul, map_neg]
  change ζ * PowerSeries.coeff m (permutationConnectedCycleSeries ζ K) =
    -PowerSeries.coeff m (formalTraceLogOneSubSeries ζ K)
  by_cases hm : m = 0
  · subst m
    rw [PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_permutationConnectedCycleSeries,
      constantCoeff_formalTraceLogOneSubSeries]
    simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [coeff_permutationConnectedCycleSeries_of_pos ζ K (n + 1) (by omega)]
    have htrace :
        PowerSeries.coeff (n + 1) (formalTraceLogOneSubSeries ζ K) =
          -(ζ ^ (n + 1) * Matrix.trace (K ^ (n + 1)) / ((n + 1 : ℕ) : ℂ)) := by
      rw [coeff_formalTraceLogOneSubSeries, coeff_log_complex_of_pos (n + 1) (by omega)]
      calc
        (-ζ) ^ (n + 1) *
              ((-1 : ℂ) ^ ((n + 1) + 1) / ((n + 1 : ℕ) : ℂ)) *
              Matrix.trace (K ^ (n + 1)) =
            ((-ζ) ^ (n + 1) * (-1 : ℂ) ^ ((n + 1) + 1)) *
              Matrix.trace (K ^ (n + 1)) / ((n + 1 : ℕ) : ℂ) := by
          ring
        _ = (-ζ ^ (n + 1)) * Matrix.trace (K ^ (n + 1)) / ((n + 1 : ℕ) : ℂ) := by
          rw [neg_pow_mul_neg_one_pow_succ]
        _ = -(ζ ^ (n + 1) * Matrix.trace (K ^ (n + 1)) / ((n + 1 : ℕ) : ℂ)) := by
          ring
    rw [htrace]
    simp only [Nat.succ_sub_one]
    rw [pow_succ]
    ring

/-- For a diagonal kernel and nonzero exchange weight, the connected-cycle series is the scaled sum
of the modewise formal logarithms `log(1 - ζ wᵢ t)`. -/
theorem permutationConnectedCycleSeries_diagonal_eq_neg_inv_smul_sum_log
    (ζ : ℂ) (w : ι → ℂ) (hζ : ζ ≠ 0) :
    permutationConnectedCycleSeries ζ (Matrix.diagonal w) =
      (-ζ⁻¹) • ∑ i : ι, PowerSeries.rescale (-ζ * w i) (PowerSeries.log ℂ) := by
  have htrace :
      formalTraceLogOneSubSeries ζ (Matrix.diagonal w) =
        ∑ i : ι, PowerSeries.rescale (-ζ * w i) (PowerSeries.log ℂ) := by
    ext m
    rw [coeff_formalTraceLogOneSubSeries, Matrix.diagonal_pow, Matrix.trace_diagonal]
    simp only [Pi.pow_apply, map_sum, PowerSeries.coeff_rescale]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow]
    ring
  have hscaled :=
    smul_permutationConnectedCycleSeries_eq_neg_traceLog ζ (Matrix.diagonal w)
  rw [htrace] at hscaled
  calc
    permutationConnectedCycleSeries ζ (Matrix.diagonal w) =
        ζ⁻¹ • (ζ • permutationConnectedCycleSeries ζ (Matrix.diagonal w)) := by
      simp [smul_smul, hζ]
    _ = ζ⁻¹ • (-∑ i : ι,
        PowerSeries.rescale (-ζ * w i) (PowerSeries.log ℂ)) := by
      rw [hscaled]
    _ = (-ζ⁻¹) • ∑ i : ι,
        PowerSeries.rescale (-ζ * w i) (PowerSeries.log ℂ) := by
      simp

end Combinatorics
