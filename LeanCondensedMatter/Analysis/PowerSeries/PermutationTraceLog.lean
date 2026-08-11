import LeanCondensedMatter.Analysis.PowerSeries.PermutationConnectedCycleSeries
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Formal trace-log interpretation of connected permutation cycles

This file completes the formal-log layer of W3 without constructing a power series over the
noncommutative matrix algebra. Mathlib's scalar `PowerSeries.log` and `PowerSeries.rescale` remain
the sole logarithm and scalar-substitution implementations. The rescaled scalar logarithm is then
paired coefficientwise with the matrix power trace `tr(K^m)`.

The resulting scalar series is the coefficientwise meaning of `tr log(1 - ζ t K)`. For `ζ ≠ 0`,
the connected-cycle series is `-(1/ζ)` times this trace-log series. The already-established
`ζ = 0` boundary remains coefficientwise and requires no division by `ζ`.
-/

namespace Combinatorics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Apply scalar power-series coefficients to the power traces of a finite matrix.

This is coefficientwise rather than an algebra homomorphism: it deliberately does not pretend that
`Matrix ι ι ℂ` is a commutative coefficient ring. -/
noncomputable def tracePowerTransform
    (K : Matrix ι ι ℂ) (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => PowerSeries.coeff m f * Matrix.trace (K ^ m)

@[simp]
theorem coeff_tracePowerTransform
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
  simp [formalTraceLogOneSubSeries]

@[simp]
theorem constantCoeff_formalTraceLogOneSubSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    PowerSeries.constantCoeff (formalTraceLogOneSubSeries ζ K) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

private theorem coeff_log_complex_of_pos (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m (PowerSeries.log ℂ) =
      (-1 : ℂ) ^ (m + 1) / (m : ℂ) := by
  rw [PowerSeries.coeff_log, if_neg (Nat.ne_of_gt hm)]
  change (((-1 : ℚ) ^ (m + 1) / (m : ℚ) : ℚ) : ℂ) =
    (-1 : ℂ) ^ (m + 1) / (m : ℂ)
  push_cast
  rfl

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

/-- Positive coefficients of the formal trace-log series are
`-ζ^m tr(K^m) / m`. -/
theorem coeff_formalTraceLogOneSubSeries_of_pos
    (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m (formalTraceLogOneSubSeries ζ K) =
      -(ζ ^ m * Matrix.trace (K ^ m) / (m : ℂ)) := by
  rw [coeff_formalTraceLogOneSubSeries, coeff_log_complex_of_pos m hm]
  calc
    (-ζ) ^ m * ((-1 : ℂ) ^ (m + 1) / (m : ℂ)) * Matrix.trace (K ^ m) =
        ((-ζ) ^ m * (-1 : ℂ) ^ (m + 1)) * Matrix.trace (K ^ m) / (m : ℂ) := by
      ring
    _ = (-ζ ^ m) * Matrix.trace (K ^ m) / (m : ℂ) := by
      rw [neg_pow_mul_neg_one_pow_succ]
    _ = -(ζ ^ m * Matrix.trace (K ^ m) / (m : ℂ)) := by ring

private theorem diagonal_pow (w : ι → ℂ) (m : ℕ) :
    Matrix.diagonal w ^ m = Matrix.diagonal (fun i => w i ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        Matrix.diagonal w ^ (m + 1) =
            Matrix.diagonal w ^ m * Matrix.diagonal w := by
          rw [pow_succ]
        _ = Matrix.diagonal (fun i => w i ^ m) * Matrix.diagonal w := by
          rw [ih]
        _ = Matrix.diagonal (fun i => w i ^ m * w i) :=
          Matrix.diagonal_mul_diagonal _ _
        _ = Matrix.diagonal (fun i => w i ^ (m + 1)) := by
          simp only [pow_succ]

private theorem trace_diagonal_pow (w : ι → ℂ) (m : ℕ) :
    Matrix.trace (Matrix.diagonal w ^ m) = ∑ i : ι, w i ^ m := by
  rw [diagonal_pow, Matrix.trace_diagonal]

/-- For a diagonal kernel, the formal trace-log decomposes into one scalar formal logarithm per
mode, for arbitrary exchange weight `ζ`. -/
theorem formalTraceLogOneSubSeries_diagonal_eq_sum_rescale_log
    (ζ : ℂ) (w : ι → ℂ) :
    formalTraceLogOneSubSeries ζ (Matrix.diagonal w) =
      ∑ i : ι, PowerSeries.rescale (-ζ * w i) (PowerSeries.log ℂ) := by
  ext m
  rw [coeff_formalTraceLogOneSubSeries, trace_diagonal_pow]
  simp only [map_sum, PowerSeries.coeff_rescale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow]
  ring

/-- Coefficientwise formal trace-log identity for nonzero exchange weight:

`C_{ζ,K}(t) = -(1/ζ) tr log(1 - ζ t K)`.

The statement is coefficientwise so the matrix algebra itself never becomes a power-series
coefficient ring. -/
theorem coeff_permutationConnectedCycleSeries_eq_neg_inv_mul_traceLog
    (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) (hζ : ζ ≠ 0) :
    PowerSeries.coeff m (permutationConnectedCycleSeries ζ K) =
      (-ζ⁻¹) * PowerSeries.coeff m (formalTraceLogOneSubSeries ζ K) := by
  by_cases hm : m = 0
  · subst m
    simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [coeff_permutationConnectedCycleSeries_of_pos ζ K (n + 1) (by omega)]
    rw [coeff_formalTraceLogOneSubSeries_of_pos ζ K (n + 1) (by omega)]
    simp only [Nat.succ_sub_one]
    rw [pow_succ]
    field_simp [hζ]
    ring

/-- Formal series form of the trace-log identity for `ζ ≠ 0`. -/
theorem permutationConnectedCycleSeries_eq_neg_inv_smul_traceLog
    (ζ : ℂ) (K : Matrix ι ι ℂ) (hζ : ζ ≠ 0) :
    permutationConnectedCycleSeries ζ K =
      (-ζ⁻¹) • formalTraceLogOneSubSeries ζ K := by
  ext m
  rw [PowerSeries.coeff_smul]
  change PowerSeries.coeff m (permutationConnectedCycleSeries ζ K) =
    (-ζ⁻¹) * PowerSeries.coeff m (formalTraceLogOneSubSeries ζ K)
  exact coeff_permutationConnectedCycleSeries_eq_neg_inv_mul_traceLog ζ K m hζ

/-- For a diagonal kernel and nonzero exchange weight, the connected-cycle series is the scaled sum
of the modewise formal logarithms `log(1 - ζ wᵢ t)`. -/
theorem permutationConnectedCycleSeries_diagonal_eq_neg_inv_smul_sum_log
    (ζ : ℂ) (w : ι → ℂ) (hζ : ζ ≠ 0) :
    permutationConnectedCycleSeries ζ (Matrix.diagonal w) =
      (-ζ⁻¹) • ∑ i : ι, PowerSeries.rescale (-ζ * w i) (PowerSeries.log ℂ) := by
  rw [permutationConnectedCycleSeries_eq_neg_inv_smul_traceLog ζ (Matrix.diagonal w) hζ]
  rw [formalTraceLogOneSubSeries_diagonal_eq_sum_rescale_log]

/-- Fermionic endpoint: at `ζ = -1`, the connected series is the formal trace of `log(1 + tK)`. -/
theorem permutationConnectedCycleSeries_neg_one_eq_traceLog
    (K : Matrix ι ι ℂ) :
    permutationConnectedCycleSeries (-1) K = formalTraceLogOneSubSeries (-1) K := by
  rw [permutationConnectedCycleSeries_eq_neg_inv_smul_traceLog (-1) K (by norm_num)]
  norm_num

/-- Bosonic endpoint: at `ζ = 1`, the connected series is minus the formal trace of
`log(1 - tK)`. -/
theorem permutationConnectedCycleSeries_one_eq_neg_traceLog
    (K : Matrix ι ι ℂ) :
    permutationConnectedCycleSeries 1 K = -formalTraceLogOneSubSeries 1 K := by
  rw [permutationConnectedCycleSeries_eq_neg_inv_smul_traceLog 1 K (by norm_num)]
  norm_num

end Combinatorics
