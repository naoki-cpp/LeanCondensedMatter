import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.Combinatorics.Cumulant.Replica
import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.Combinatorics.SetPartition.DistinguishedBlock
import Mathlib.RingTheory.PowerSeries.Derivative

set_option linter.style.header false

/-!
# Replica-count polynomials and finite-set connected expansions

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
    rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
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
      simp only [Nat.succ_ne_zero, ite_false]
      simp [Nat.factorial_succ, pow_succ, div_eq_mul_inv]
      have hkfac : (k.factorial : R) ≠ 0 :=
        Nat.cast_ne_zero.mpr k.factorial_ne_zero
      field_simp [hkfac]
      change (-1 : R) ^ k = algebraMap ℚ R ((-1 : ℚ) ^ k)
      rw [map_pow]
      simp

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
  field_simp [hkfac]
  ring

end PowerSeries

/-!
## Replica bridge between formal power series and finite-set connected expansions

This file identifies the fixed-order power-series replica polynomial with the finite-set replica
polynomial under the forward moment relation.  The proof uses only distinguished-block recursion,
moment expansion, and Stirling multiplicities; it does not use cumulant inversion.
-/

open scoped BigOperators

namespace Combinatorics

open PowerSeries

variable {α R : Type*} [DecidableEq α] [Field R] [CharZero R]

private noncomputable def egfBlockCoeff (Z : PowerSeries R) (n k : ℕ) : R :=
  ((n.factorial : R) / (k.factorial : R)) * coeff n ((Z - 1) ^ k)

private theorem egfBlockCoeff_succ_succ
    (Z : PowerSeries R) (n k : ℕ) :
    egfBlockCoeff Z (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : R) *
          (((j + 1).factorial : R) * coeff (j + 1) Z) *
          egfBlockCoeff Z (n - j) k := by
  let U : PowerSeries R := Z - 1
  have hderiv := congrArg (coeff n) (PowerSeries.derivative_pow U (k + 1))
  rw [PowerSeries.coeff_derivative, Nat.add_sub_cancel] at hderiv
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hderiv
  have hnatCoeff : ∀ i : ℕ,
      coeff i (((k + 1 : ℕ) : PowerSeries R) * U ^ k) =
        (k + 1 : R) * coeff i (U ^ k) := by
    intro i
    rw [← map_natCast (PowerSeries.C : R →+* PowerSeries R) (k + 1),
      PowerSeries.coeff_C_mul]
    simp [Nat.cast_add, Nat.cast_one]
  simp_rw [hnatCoeff, PowerSeries.coeff_derivative] at hderiv
  have hderiv' :
      (n + 1 : R) * coeff (n + 1) ((Z - 1) ^ (k + 1)) =
        (k + 1 : R) *
          ∑ i ∈ Finset.range (n + 1),
            coeff i (U ^ k) * (coeff (n - i + 1) U * (((n - i : ℕ) : R) + 1)) := by
    calc
      (n + 1 : R) * coeff (n + 1) ((Z - 1) ^ (k + 1)) =
          coeff (n + 1) (U ^ (k + 1)) * (n + 1 : R) := by
            simp [U, mul_comm]
      _ = ∑ i ∈ Finset.range (n + 1),
          (k + 1 : R) * coeff i (U ^ k) *
            (coeff (n - i + 1) U * (((n - i : ℕ) : R) + 1)) := by
            simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using hderiv
      _ = (k + 1 : R) *
          ∑ i ∈ Finset.range (n + 1),
            coeff i (U ^ k) * (coeff (n - i + 1) U * (((n - i : ℕ) : R) + 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  have hmain :
      egfBlockCoeff Z (n + 1) (k + 1) =
        ((n.factorial : R) / (k.factorial : R)) *
          ∑ i ∈ Finset.range (n + 1),
            coeff i (U ^ k) * (coeff (n - i + 1) U * (((n - i : ℕ) : R) + 1)) := by
    rw [egfBlockCoeff]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hkfac : (k.factorial : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k + 1 : R) ≠ 0 := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : R) ≠ 0)
    field_simp [hkfac, hk1]
    calc
      (n + 1 : R) * (n.factorial : R) *
          coeff (n + 1) ((Z - 1) ^ (k + 1)) =
          (n.factorial : R) *
            ((n + 1 : R) * coeff (n + 1) ((Z - 1) ^ (k + 1))) := by
              ring
      _ = (n.factorial : R) *
          ((k + 1 : R) *
            ∑ i ∈ Finset.range (n + 1),
              coeff i (U ^ k) *
                (coeff (n - i + 1) U * (((n - i : ℕ) : R) + 1))) := by
              rw [hderiv']
      _ = _ := by ring
  rw [hmain, Finset.mul_sum]
  have hreflect :
      (∑ i ∈ Finset.range (n + 1),
          ((n.factorial : R) / (k.factorial : R)) *
            (coeff i (U ^ k) * (coeff (n - i + 1) U * (((n - i : ℕ) : R) + 1)))) =
        ∑ j ∈ Finset.range (n + 1),
          ((n.factorial : R) / (k.factorial : R)) *
            (coeff (n - j) (U ^ k) * (coeff (j + 1) U * (j + 1 : R))) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hpred : n + 1 - 1 = n := by omega
    have hsub : n - (n - j) = j := by omega
    rw [hpred, hsub]
  rw [hreflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hcoeff : coeff (j + 1) U = coeff (j + 1) Z := by
    simp [U]
  rw [hcoeff, egfBlockCoeff]
  have hchoose := Nat.choose_mul_factorial_mul_factorial hjn
  have hchooseR :
      (n.factorial : R) =
        (n.choose j : R) * (j.factorial : R) * ((n - j).factorial : R) := by
    norm_cast
    exact hchoose.symm
  have hkfac : (k.factorial : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hkfac]
  rw [hchooseR]
  ring

omit [CharZero R] in
private theorem partitionProduct_partsCardSuccEquiv_symm
    (m : Finset α → R) {s : Finset α} {a : α} (ha : a ∈ s) (k : ℕ)
    (x : Σ B : Finpartition.BlockContaining s a,
      {Q : Finpartition (s \ B.1) // Q.parts.card = k}) :
    Finpartition.partitionProduct m
        ((Finpartition.partsCardSuccEquiv ha k).symm x).1 =
      m x.1.1 * Finpartition.partitionProduct m x.2.1 := by
  rcases x with ⟨B, Q⟩
  change
    Finpartition.partitionProduct m
      ((Finpartition.distinguishedBlockEquiv s a ha).symm ⟨B, Q.1⟩) =
        m B.1 * Finpartition.partitionProduct m Q.1
  exact Finpartition.partitionProduct_distinguishedBlockEquiv_symm m ha ⟨B, Q.1⟩

private theorem egfBlockCoeff_eq_fixedBlockMomentSum
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1)
    (s : Finset α) (k : ℕ) :
    egfBlockCoeff Z s.card k =
      ∑ π : {π : Finpartition s // π.parts.card = k},
        Finpartition.partitionProduct
          (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) π.1 := by
  classical
  revert k
  refine Finset.strongInductionOn s ?_
  intro s ih k
  by_cases hs : s = ∅
  · subst s
    cases k with
    | zero =>
        letI : Unique (Finpartition (∅ : Finset α)) :=
          inferInstanceAs (Unique (Finpartition (⊥ : Finset α)))
        letI : Unique {π : Finpartition (∅ : Finset α) // π.parts.card = 0} := {
          default := ⟨default, by simp⟩
          uniq := by
            intro π
            apply Subtype.ext
            exact Subsingleton.elim _ _
        }
        have hparts :
            (default :
              {π : Finpartition (∅ : Finset α) // π.parts.card = 0}).1.parts = ∅ := by
          exact (Finpartition.parts_eq_empty_iff
            (P := (default :
              {π : Finpartition (∅ : Finset α) // π.parts.card = 0}).1)).2 rfl
        simp [egfBlockCoeff, Finpartition.partitionProduct, hparts]
    | succ k =>
        letI : IsEmpty {π : Finpartition (∅ : Finset α) // π.parts.card = k + 1} :=
          ⟨fun π => by
            have hparts : π.1.parts = ∅ :=
              (Finpartition.parts_eq_empty_iff (P := π.1)).2 rfl
            have hcard : π.1.parts.card = 0 := by simp [hparts]
            exact Nat.ne_of_gt (Nat.zero_lt_succ k) (π.2.symm.trans hcard)⟩
        simp [egfBlockCoeff, coeff_zero_eq_constantCoeff, hZ]
  · cases k with
    | zero =>
        letI : IsEmpty {π : Finpartition s // π.parts.card = 0} :=
          ⟨fun π => by
            have hne : π.1.parts.Nonempty := π.1.parts_nonempty hs
            exact (Finset.card_ne_zero.mpr hne) π.2⟩
        have hpos : 0 < s.card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        simp [egfBlockCoeff, hpos.ne']
    | succ k =>
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        rw [← Equiv.sum_comp (Finpartition.partsCardSuccEquiv ha k).symm]
        rw [Fintype.sum_sigma]
        simp_rw [partitionProduct_partsCardSuccEquiv_symm
          (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) ha k]
        have hsmall : ∀ B : Finpartition.BlockContaining s a,
            (∑ Q : {Q : Finpartition (s \ B.1) // Q.parts.card = k},
                Finpartition.partitionProduct
                  (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) Q.1) =
              egfBlockCoeff Z (s \ B.1).card k := by
          intro B
          exact (ih (s \ B.1) (Finset.sdiff_ssubset B.2.1 ⟨a, B.2.2⟩) k).symm
        have hcollapse :
            (∑ B : Finpartition.BlockContaining s a,
              ∑ Q : {Q : Finpartition (s \ B.1) // Q.parts.card = k},
                ((B.1.card.factorial : R) * coeff B.1.card Z) *
                  Finpartition.partitionProduct
                    (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) Q.1) =
              ∑ B : Finpartition.BlockContaining s a,
                ((B.1.card.factorial : R) * coeff B.1.card Z) *
                  egfBlockCoeff Z (s \ B.1).card k := by
          apply Fintype.sum_congr
          intro B
          rw [← hsmall B, Finset.mul_sum]
        rw [hcollapse]
        symm
        calc
          (∑ B : Finpartition.BlockContaining s a,
              ((B.1.card.factorial : R) * coeff B.1.card Z) *
                egfBlockCoeff Z (s \ B.1).card k) =
              ∑ B : Finpartition.BlockContaining s a,
                ((B.1.card.factorial : R) * coeff B.1.card Z) *
                  egfBlockCoeff Z (s.card - B.1.card) k := by
                    apply Fintype.sum_congr
                    intro B
                    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr B.2.1]
          _ = ∑ j ∈ Finset.range s.card,
              (Nat.choose (s.card - 1) j : R) *
                (((j + 1).factorial : R) * coeff (j + 1) Z *
                  egfBlockCoeff Z (s.card - (j + 1)) k) := by
                    simpa [mul_assoc] using
                      Finpartition.sum_blockContaining_card s a ha
                        (fun b => ((b.factorial : R) * coeff b Z) *
                          egfBlockCoeff Z (s.card - b) k)
          _ = egfBlockCoeff Z s.card (k + 1) := by
                have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
                have hcard : s.card = (s.card - 1) + 1 := by
                  omega
                rw [hcard]
                simpa [Nat.add_sub_add_right, mul_assoc] using
                  (egfBlockCoeff_succ_succ (R := R) Z (s.card - 1) k).symm

/-- The falling-factorial coefficient in the power-series replica polynomial is the sum of
products of factorial-normalized moments over set partitions with the corresponding number of
blocks. -/
theorem replicaCoeffPolynomial_descPochhammerCoeff_eq_fixedBlockMomentSum
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1)
    (s : Finset α) (k : ℕ) :
    (((s.card.factorial : R) / (k.factorial : R)) *
        coeff s.card ((Z - 1) ^ k)) =
      ∑ π : {π : Finpartition s // π.parts.card = k},
        Finpartition.partitionProduct
          (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) π.1 := by
  exact egfBlockCoeff_eq_fixedBlockMomentSum hZ s k


/-- Under the forward finite-set moment relation, the fixed-order power-series replica polynomial
is exactly the finite-set replica polynomial.  This is the algebraic bridge between the two replica
constructions and uses no moment-cumulant inversion. -/
theorem replicaCoeffPolynomial_eq_replicaPolynomial
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1)
    (κ : Finset α → R) (s : Finset α)
    (hMoment : ∀ T : Finset α,
      (T.card.factorial : R) * coeff T.card Z =
        Finpartition.momentFromCumulant κ T) :
    PowerSeries.replicaCoeffPolynomial Z s.card =
      Finpartition.replicaPolynomial κ s := by
  classical
  rw [PowerSeries.replicaCoeffPolynomial,
    Finpartition.replicaPolynomial_eq_sum_descPochhammer_stirling]
  apply Finset.sum_congr rfl
  intro k hk
  have hmfun :
      (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) =
        Finpartition.momentFromCumulant κ := by
    funext T
    exact hMoment T
  have hcoeff :
      (((s.card.factorial : R) / (k.factorial : R)) *
          coeff s.card ((Z - 1) ^ k)) =
        ∑ ρ : Finpartition s,
          (Nat.stirlingSecond ρ.parts.card k : R) *
            Finpartition.partitionProduct κ ρ := by
    calc
      (((s.card.factorial : R) / (k.factorial : R)) *
          coeff s.card ((Z - 1) ^ k)) =
          ∑ π : {π : Finpartition s // π.parts.card = k},
            Finpartition.partitionProduct
              (fun T : Finset α => (T.card.factorial : R) * coeff T.card Z) π.1 :=
        replicaCoeffPolynomial_descPochhammerCoeff_eq_fixedBlockMomentSum hZ s k
      _ = ∑ π : {π : Finpartition s // π.parts.card = k},
            Finpartition.partitionProduct (Finpartition.momentFromCumulant κ) π.1 := by
              rw [hmfun]
      _ = ∑ ρ : Finpartition s,
            (Nat.stirlingSecond ρ.parts.card k : R) *
              Finpartition.partitionProduct κ ρ :=
        Finpartition.sum_partitionProduct_momentFromCumulant_partsCard_eq κ s k
  rw [hcoeff]


/-- Replica-method form of the generic formal linked-cluster theorem.  If the
factorial-normalized coefficients of a unit-constant formal power series are the object moments of
a multiplicative connected decomposition, then the factorial-normalized formal-log coefficient is
the connected contribution.  The proof factors through the equality of the two replica
polynomials, not through cumulant inversion. -/
theorem factorial_mul_coeff_logOf_eq_connectedContribution_replica
    {Z : PowerSeries R} (hZ : constantCoeff Z = 1)
    {D : ConnectedDecomposition α} (W : MultiplicativeWeight D R)
    (hMoment :
      powerSeriesMomentSetFunction (α := α) Z hZ = W.normalizedObjectMoment)
    {s : Finset α} (hs : s ≠ ∅) :
    (s.card.factorial : R) * coeff s.card (logOf Z) =
      W.connectedContribution s := by
  have hMomentCoeff :
      ∀ T : Finset α, powerSeriesMomentCoeff Z T.card = W.normalizedObjectMoment T :=
    (powerSeriesMomentSetFunction_eq_iff Z hZ W.normalizedObjectMoment).mp hMoment
  have hpoly := congrArg (fun p : Polynomial R => p.coeff 1)
    (replicaCoeffPolynomial_eq_replicaPolynomial hZ W.connectedContribution s (fun T => by
      calc
        (T.card.factorial : R) * coeff T.card Z = W.objectMoment T := by
          simpa only [powerSeriesMomentCoeff,
            MultiplicativeWeight.normalizedObjectMoment_apply] using hMomentCoeff T
        _ = Finpartition.momentFromCumulant W.connectedContribution T :=
          W.objectMoment_eq_momentFromCumulant T))
  rw [PowerSeries.replicaCoeffPolynomial_coeff_one hZ s.card,
    Finpartition.replicaPolynomial_coeff_one W.connectedContribution hs] at hpoly
  exact hpoly

end Combinatorics
