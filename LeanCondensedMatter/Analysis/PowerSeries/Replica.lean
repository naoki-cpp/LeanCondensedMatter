import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Log
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

variable {R : Type*} [Field R]

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
theorem replicaCoeffPolynomial_eval_nat [CharZero R]
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


private theorem coeff_one_descPochhammer_succ (k : ℕ) :
    (descPochhammer R (k + 1)).coeff 1 = (-1 : R) ^ k * (k.factorial : R) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [descPochhammer_succ_right]
      rw [← Polynomial.C_eq_natCast (R := R) (k + 1)]
      rw [show 1 = 0 + 1 by rfl, Polynomial.coeff_mul_X_sub_C]
      rw [Polynomial.coeff_zero_eq_eval_zero,
        descPochhammer_ne_zero_eval_zero (R := R) (Nat.succ_ne_zero k), ih]
      simp [Nat.factorial_succ, pow_succ]
      ring

private theorem inv_factorial_mul_coeff_one_descPochhammer [CharZero R] (k : ℕ) :
    (k.factorial : R)⁻¹ * (descPochhammer R k).coeff 1 =
      coeff k (log R) := by
  cases k with
  | zero => simp [Polynomial.coeff_one]
  | succ k =>
      rw [coeff_one_descPochhammer_succ, coeff_log]
      simp only [Nat.succ_ne_zero, if_false]
      simp [Nat.factorial_succ, pow_succ, div_eq_mul_inv]
      have hkfac : (k.factorial : R) ≠ 0 :=
        Nat.cast_ne_zero.mpr k.factorial_ne_zero
      field_simp [hkfac] <;> ring

/-- The coefficient linear in the formal replica count is the factorial-normalized coefficient
of the formal logarithm. This is the algebraic replica identity, with no analytic continuation in
the replica number. -/
theorem replicaCoeffPolynomial_coeff_one [CharZero R]
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1) (m : ℕ) :
    (replicaCoeffPolynomial Z m).coeff 1 =
      (m.factorial : R) * coeff m (logOf Z) := by
  let U : PowerSeries R := Z - 1
  have hU : HasSubst U :=
    HasSubst.of_constantCoeff_zero' (by simp [U, hZ])
  have hLog :
      coeff m (logOf Z) =
        ∑ k ∈ Finset.range (m + 1), coeff k (log R) * coeff m (U ^ k) := by
    rw [logOf_eq, coeff_subst' hU]
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (m + 1))]
    · simp only [smul_eq_mul]
    · intro k hk
      change coeff k (log R) • coeff m (U ^ k) ≠ 0 at hk
      apply Finset.mem_range.mpr
      by_contra hkm
      have hmk : m < k := Nat.succ_le_iff.mp (Nat.le_of_not_gt hkm)
      have hzero : coeff m (U ^ k) = 0 := by
        simpa [U] using coeff_sub_one_pow_eq_zero_of_lt hZ hmk
      exact hk (by simp [hzero])
  rw [replicaCoeffPolynomial, Polynomial.finsetSum_coeff, hLog, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_C_mul]
  rw [← inv_factorial_mul_coeff_one_descPochhammer (R := R) k]
  have hkfac : (k.factorial : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp [hkfac] <;> ring

end PowerSeries
