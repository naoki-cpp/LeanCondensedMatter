import LeanCondensedMatter.Permutation.AssignmentCycleTrace
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Formal trace-log interpretation of connected permutation cycles

The connected-cycle series packages the EGF-normalized assignment-summed single-cycle
contributions and identifies them with scalar matrix power traces. No power series over the
noncommutative matrix algebra is constructed. Mathlib's scalar `PowerSeries.log` and `PowerSeries.rescale` remain
the sole logarithm and scalar-substitution implementations. The rescaled scalar logarithm is then
paired coefficientwise with the matrix power trace `tr(K^m)`.

The resulting scalar series is the coefficientwise meaning of `tr log(1 - ζ t K)`. The canonical
identity is division-free: multiplying the connected-cycle series by `ζ` gives the negative
trace-log series for every exchange weight, including `ζ = 0`. Division by `ζ` appears only in
nonzero-weight specializations.
-/

namespace Combinatorics

variable {ι : Type*} [Fintype ι]

/-- The formal connected-cycle series associated with exchange weight `ζ` and finite kernel `K`.

Its constant coefficient is zero. At positive order `m`, its coefficient is the EGF-normalized
assignment-summed one-cycle contribution. -/
noncomputable def permutationConnectedCycleSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m =>
    if m = 0 then 0
    else
      (∑ x : Fin m → ι,
        singleCycleContribution ζ (fun a b : Fin m => K (x a) (x b)) Finset.univ) /
          (Nat.factorial m : ℂ)

@[simp]
theorem constantCoeff_permutationConnectedCycleSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    PowerSeries.constantCoeff (permutationConnectedCycleSeries ζ K) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [permutationConnectedCycleSeries]

/-- Positive coefficients of the formal connected-cycle series are the universal cyclic trace
coefficients `ζ^(m-1) tr(K^m) / m`. -/
theorem coeff_permutationConnectedCycleSeries_of_pos
    [DecidableEq ι] (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m (permutationConnectedCycleSeries ζ K) =
      ζ ^ (m - 1) * Matrix.trace (K ^ m) / (m : ℂ) := by
  rw [permutationConnectedCycleSeries, PowerSeries.coeff_mk]
  rw [ite_eq_right (Nat.ne_of_gt hm)]
  rw [sum_singleCycleContribution_assignments_eq_factorial_mul_trace ζ K m hm]
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hm)]
  push_cast
  have hm0 : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  have hfac0 : (Nat.factorial (m - 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - 1)
  field_simp [hm0, hfac0] <;> ring


variable [DecidableEq ι]

/-- The formal scalar series representing `tr log(1 - ζ t K)` through matrix power traces.

`PowerSeries.rescale (-ζ)` is Mathlib's substitution `f(X) ↦ f(-ζ X)`, so this definition uses
Mathlib's `log(1 + X)` directly rather than reimplementing logarithm coefficients. -/
noncomputable def formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m =>
    PowerSeries.coeff m (PowerSeries.rescale (-ζ) (PowerSeries.log ℂ)) * Matrix.trace (K ^ m)

@[simp]
theorem coeff_formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) :
    PowerSeries.coeff m (formalTraceLogOneSubSeries ζ K) =
      (-ζ) ^ m * PowerSeries.coeff m (PowerSeries.log ℂ) * Matrix.trace (K ^ m) := by
  simp [formalTraceLogOneSubSeries]

@[simp]
theorem constantCoeff_formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    PowerSeries.constantCoeff (formalTraceLogOneSubSeries ζ K) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

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
      rw [coeff_formalTraceLogOneSubSeries, PowerSeries.coeff_log,
        ite_eq_right (Nat.succ_ne_zero n)]
      change (-ζ) ^ (n + 1) *
          (((-1 : ℚ) ^ ((n + 1) + 1) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℂ) *
          Matrix.trace (K ^ (n + 1)) = _
      rw [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
      calc
        (-ζ) ^ (n + 1) *
              ((-1 : ℂ) ^ ((n + 1) + 1) / ((n + 1 : ℕ) : ℂ)) *
              Matrix.trace (K ^ (n + 1)) =
            ((-ζ) ^ (n + 1) * (-1 : ℂ) ^ ((n + 1) + 1)) *
              Matrix.trace (K ^ (n + 1)) / ((n + 1 : ℕ) : ℂ) := by
          ring
        _ = (-ζ ^ (n + 1)) * Matrix.trace (K ^ (n + 1)) / ((n + 1 : ℕ) : ℂ) := by
          rw [pow_succ (-1 : ℂ), ← mul_assoc, ← mul_pow]
          simp
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
