import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Replica-count polynomials for formal power series

At fixed perturbation order, the coefficient of a normalized power series raised to an integer
replica number is polynomial in that replica number.  The falling-factorial basis makes this
polynomial finite without introducing an analytic continuation in the replica count.
-/

open scoped BigOperators

namespace PowerSeries

/-- At fixed perturbation order `m`, the polynomial dependence of the factorial-normalized
coefficient of `Z^n` on the replica number `n`.

The falling-factorial basis records the binomial expansion of `Z^n = (1 + (Z - 1))^n`. -/
noncomputable def replicaCoeffPolynomial (Z : PowerSeries ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C
        (((m.factorial : ℂ) / (k.factorial : ℂ)) * coeff m ((Z - 1) ^ k)) *
      descPochhammer ℂ k

private theorem coeff_sub_one_pow_eq_zero_of_lt
    {Z : PowerSeries ℂ} (hZ : constantCoeff Z = 1) {m k : ℕ} (h : m < k) :
    coeff m ((Z - 1) ^ k) = 0 := by
  apply coeff_of_lt_order
  exact (ENat.natCast_lt_natCast.mpr h).trans_le
    (le_order_pow_of_constantCoeff_eq_zero k (by simp [hZ]))

private theorem descPochhammer_eval_nat (n k : ℕ) :
    (descPochhammer ℂ k).eval (n : ℂ) =
      (k.factorial : ℂ) * (n.choose k : ℂ) := by
  rw [descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

/-- Evaluating the fixed-order replica polynomial at a natural replica number gives the
factorial-normalized coefficient of the corresponding power of the series. -/
theorem replicaCoeffPolynomial_eval_nat
    {Z : PowerSeries ℂ} (hZ : constantCoeff Z = 1) (m n : ℕ) :
    (replicaCoeffPolynomial Z m).eval (n : ℂ) =
      (m.factorial : ℂ) * coeff m (Z ^ n) := by
  let U : PowerSeries ℂ := Z - 1
  have hEval :
      (replicaCoeffPolynomial Z m).eval (n : ℂ) =
        (m.factorial : ℂ) *
          ∑ k ∈ Finset.range (m + 1),
            (n.choose k : ℂ) * coeff m (U ^ k) := by
    rw [replicaCoeffPolynomial, Polynomial.eval_finsetSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_nat]
    change
      (((m.factorial : ℂ) / (k.factorial : ℂ)) * coeff m (U ^ k)) *
          ((k.factorial : ℂ) * (n.choose k : ℂ)) =
        (m.factorial : ℂ) * ((n.choose k : ℂ) * coeff m (U ^ k))
    have hkfac : (k.factorial : ℂ) ≠ 0 := by
      exact_mod_cast k.factorial_ne_zero
    field_simp [hkfac]
    ring
  have hPow :
      coeff m (Z ^ n) =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * coeff m (U ^ k) := by
    have hZU : Z = U + 1 := by
      simp [U]
    rw [hZU, add_pow]
    simp only [map_sum, one_pow, mul_one, coeff_mul_natCast]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hTruncate :
      (∑ k ∈ Finset.range (m + 1),
          (n.choose k : ℂ) * coeff m (U ^ k)) =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * coeff m (U ^ k) := by
    rcases le_total n m with hnm | hmn
    · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnm))
      intro k hkm hkn
      have hnk : n < k := by
        have hkge : n + 1 ≤ k := by
          exact Nat.le_of_not_gt (by
            intro hklt
            exact hkn (Finset.mem_range.mpr hklt))
        omega
      rw [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, zero_mul]
    · symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmn))
      intro k hkn hkm
      have hmk : m < k := by
        have hkge : m + 1 ≤ k := by
          exact Nat.le_of_not_gt (by
            intro hklt
            exact hkm (Finset.mem_range.mpr hklt))
        omega
      rw [coeff_sub_one_pow_eq_zero_of_lt hZ hmk, mul_zero]
  rw [hEval, hTruncate, ← hPow]

end PowerSeries
