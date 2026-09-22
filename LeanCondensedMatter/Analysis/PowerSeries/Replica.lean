import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Replica-count polynomials for formal power series

At fixed perturbation order, the coefficient of a normalized power series raised to an integer
replica number is polynomial in that replica number.  The falling-factorial basis makes this
polynomial finite without introducing an analytic continuation in the replica count.
-/

open scoped BigOperators

namespace PowerSeries

variable {R : Type*} [Field R] [CharZero R]

/-- At fixed perturbation order `m`, the polynomial dependence of the factorial-normalized
coefficient of `Z^n` on the replica number `n`.

The falling-factorial basis records the binomial expansion of `Z^n = (1 + (Z - 1))^n`. -/
noncomputable def replicaCoeffPolynomial (Z : PowerSeries R) (m : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C
        (((m.factorial : R) / (k.factorial : R)) * coeff m ((Z - 1) ^ k)) *
      descPochhammer R k

private theorem coeff_sub_one_pow_eq_zero_of_lt
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1) {m k : ℕ} (h : m < k) :
    coeff m ((Z - 1) ^ k) = 0 := by
  apply coeff_of_lt_order
  exact (ENat.natCast_lt_natCast.mpr h).trans_le
    (le_order_pow_of_constantCoeff_eq_zero k (by simp [hZ]))

private theorem descPochhammer_eval_nat (n k : ℕ) :
    (descPochhammer R k).eval (n : R) =
      (k.factorial : R) * (n.choose k : R) := by
  rw [descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

/-- Evaluating the fixed-order replica polynomial at a natural replica number gives the
factorial-normalized coefficient of the corresponding power of the series. -/
theorem replicaCoeffPolynomial_eval_nat
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1) (m n : ℕ) :
    (replicaCoeffPolynomial Z m).eval (n : R) =
      (m.factorial : R) * coeff m (Z ^ n) := by
  let U : PowerSeries R := Z - 1
  have hEval :
      (replicaCoeffPolynomial Z m).eval (n : R) =
        (m.factorial : R) *
          ∑ k ∈ Finset.range (m + 1),
            (n.choose k : R) * coeff m (U ^ k) := by
    rw [replicaCoeffPolynomial, Polynomial.eval_finsetSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_nat]
    change
      (((m.factorial : R) / (k.factorial : R)) * coeff m (U ^ k)) *
          ((k.factorial : R) * (n.choose k : R)) =
        (m.factorial : R) * ((n.choose k : R) * coeff m (U ^ k))
    have hkfac : (k.factorial : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp [hkfac]
  have hPow :
      coeff m (Z ^ n) =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : R) * coeff m (U ^ k) := by
    have hZU : Z = U + 1 := by
      simp [U]
    rw [hZU, add_pow]
    simp only [map_sum, one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k hk
    change coeff m (U ^ k * C (n.choose k : R)) =
      (n.choose k : R) * coeff m (U ^ k)
    rw [coeff_mul_C]
    ring
  have hTruncate :
      (∑ k ∈ Finset.range (m + 1),
          (n.choose k : R) * coeff m (U ^ k)) =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : R) * coeff m (U ^ k) := by
    rcases le_total n m with hnm | hmn
    · symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnm))
      intro k hkm hkn
      have hnk : n < k := by
        simp only [Finset.mem_range] at hkm hkn
        exact Nat.lt_of_not_ge fun hk =>
          hkn (Nat.lt_succ_of_le hk)
      rw [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, zero_mul]
    · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmn))
      intro k hkn hkm
      have hmk : m < k := by
        simp only [Finset.mem_range] at hkn hkm
        exact Nat.lt_of_not_ge fun hk =>
          hkm (Nat.lt_succ_of_le hk)
      rw [coeff_sub_one_pow_eq_zero_of_lt hZ hmk, mul_zero]
  rw [hEval, hTruncate, ← hPow]

end PowerSeries
