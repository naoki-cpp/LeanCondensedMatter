import LeanCondensedMatter.Combinatorics.MomentCumulant
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Formal-log coefficients and finite-set cumulants

This file identifies the factorial-normalized coefficients of the formal logarithm of a normalized
power series with the finite-set cumulants of its factorial-normalized coefficients. The proof avoids
an explicit closed formula for the partition-lattice Möbius function. Instead, it proves the same
binomial recurrence on both sides: formally from `(log Z)' * Z = Z'`, and combinatorially by splitting
a set partition at the block containing a distinguished element.
-/

open scoped BigOperators

namespace Finpartition

variable {α : Type*} [DecidableEq α]

/-- A nonempty subset of `s` containing the distinguished element `a`. -/
private def BlockContaining (s : Finset α) (a : α) :=
  {B : Finset α // B ⊆ s ∧ a ∈ B}

private theorem insert_part_parts_avoid {s : Finset α} (P : Finpartition s) {a : α}
    (ha : a ∈ s) :
    insert (P.part a) (P.avoid (P.part a)).parts = P.parts := by
  classical
  ext B
  constructor
  · intro hB
    rcases Finset.mem_insert.mp hB with hB | hB
    · simpa [hB] using P.part_mem.mpr ha
    · rw [P.mem_avoid] at hB
      obtain ⟨C, hC, hCle, hCB⟩ := hB
      have hCne : C ≠ P.part a := by
        intro h
        subst C
        exact hCle le_rfl
      have hdisj : Disjoint C (P.part a) :=
        P.disjoint hC (P.part_mem.mpr ha) hCne
      rw [hdisj.sdiff_eq_left] at hCB
      simpa [← hCB] using hC
  · intro hB
    by_cases hEq : B = P.part a
    · exact Finset.mem_insert.mpr (Or.inl hEq)
    · apply Finset.mem_insert.mpr
      right
      rw [P.mem_avoid]
      have hdisj : Disjoint B (P.part a) :=
        P.disjoint hB (P.part_mem.mpr ha) hEq
      refine ⟨B, hB, ?_, hdisj.sdiff_eq_left⟩
      intro hle
      exact P.ne_bot hB (hdisj.eq_bot_of_le hle)

private theorem avoid_extend_eq {s B : Finset α} {a : α}
    (hBsub : B ⊆ s) (haB : a ∈ B) (Q : Finpartition (s \ B)) :
    (Q.extend (Finset.ne_empty_of_mem haB) disjoint_sdiff_self_left
      (by simpa [sup_comm] using sup_sdiff_cancel_right hBsub)).avoid B = Q := by
  classical
  apply Finpartition.ext
  ext C
  constructor
  · intro hC
    rw [Finpartition.mem_avoid] at hC
    obtain ⟨D, hD, hDle, hDC⟩ := hC
    change D ∈ insert B Q.parts at hD
    rcases Finset.mem_insert.mp hD with hDB | hDQ
    · subst D
      exact (hDle le_rfl).elim
    · have hdisj : Disjoint D B :=
        disjoint_sdiff_self_left.mono_left (Q.le hDQ)
      rw [hdisj.sdiff_eq_left] at hDC
      simpa [← hDC] using hDQ
  · intro hC
    rw [Finpartition.mem_avoid]
    have hdisj : Disjoint C B :=
      disjoint_sdiff_self_left.mono_left (Q.le hC)
    refine ⟨C, Finset.mem_insert.mpr (Or.inr hC), ?_, hdisj.sdiff_eq_left⟩
    intro hle
    exact Q.ne_bot hC (hdisj.eq_bot_of_le hle)

/-- A partition is equivalent to its distinguished block and a partition of the complement. -/
private def partComplementEquiv (s : Finset α) (a : α) (ha : a ∈ s) :
    Finpartition s ≃ Σ B : BlockContaining s a, Finpartition (s \ (B : Finset α)) where
  toFun P := ⟨⟨P.part a, P.part_subset a, P.mem_part ha⟩, P.avoid (P.part a)⟩
  invFun x := x.2.extend (Finset.ne_empty_of_mem x.1.2.2) disjoint_sdiff_self_left
    (by simpa [sup_comm] using sup_sdiff_cancel_right x.1.2.1)
  left_inv P := by
    apply Finpartition.ext
    change insert (P.part a) (P.avoid (P.part a)).parts = P.parts
    exact insert_part_parts_avoid P ha
  right_inv x := by
    rcases x with ⟨B, Q⟩
    let P := Q.extend (Finset.ne_empty_of_mem B.2.2) disjoint_sdiff_self_left
      (by simpa [sup_comm] using sup_sdiff_cancel_right B.2.1)
    have hBmem : (B : Finset α) ∈ P.parts := by
      exact Finset.mem_insert_self _ _
    have hpart : P.part a = B := P.part_eq_of_mem hBmem B.2.2
    apply Sigma.ext hpart
    apply heq_of_eq
    exact avoid_extend_eq B.2.1 B.2.2 Q

private theorem partitionProduct_partComplementEquiv_symm
    (κ : Finset α → ℂ) {s : Finset α} {a : α} (ha : a ∈ s)
    (x : Σ B : BlockContaining s a, Finpartition (s \ (B : Finset α))) :
    partitionProduct κ ((partComplementEquiv s a ha).symm x) =
      κ x.1 * partitionProduct κ x.2 := by
  classical
  rcases x with ⟨B, Q⟩
  change (∏ C ∈ insert (B : Finset α) Q.parts, κ C) =
    κ B * ∏ C ∈ Q.parts, κ C
  rw [Finset.prod_insert]
  intro hB
  have hBsub : (B : Finset α) ⊆ s \ B := Q.le hB
  exact Finset.ne_empty_of_mem B.2.2
    (Finset.eq_empty_iff_forall_not_mem.mpr fun x hx =>
      (Finset.mem_sdiff.mp (hBsub hx)).2 hx)

/-- The moment sum splits by the block containing a distinguished element. -/
theorem momentFromCumulant_eq_sum_blockContaining (κ : Finset α → ℂ)
    {s : Finset α} {a : α} (ha : a ∈ s) :
    momentFromCumulant κ s =
      ∑ B : BlockContaining s a,
        κ B * momentFromCumulant κ (s \ (B : Finset α)) := by
  classical
  rw [momentFromCumulant, ← Equiv.sum_comp (partComplementEquiv s a ha).symm,
    Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro B
  simp_rw [partitionProduct_partComplementEquiv_symm κ ha]
  rw [← Finset.mul_sum]
  rfl

private def blockContainingEquivPowerset (s : Finset α) (a : α) (ha : a ∈ s) :
    BlockContaining s a ≃ {T : Finset α // T ∈ (s.erase a).powerset} where
  toFun B := ⟨B.1.erase a, by
    rw [Finset.mem_powerset]
    intro x hx
    have hxB : x ∈ B := Finset.mem_of_mem_erase hx
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, B.2.1 hxB⟩⟩
  invFun T := ⟨insert a T.1, by
    constructor
    · rw [Finset.insert_subset_iff]
      exact ⟨ha, (Finset.mem_powerset.mp T.2).trans (Finset.erase_subset _ _)⟩
    · exact Finset.mem_insert_self _ _⟩
  left_inv B := by
    apply Subtype.ext
    exact Finset.insert_erase B.2.2
  right_inv T := by
    apply Subtype.ext
    simp only
    rw [Finset.erase_insert]
    exact fun haT => (Finset.mem_powerset.mp T.2 haT).1 rfl

private theorem sum_blockContaining_card (s : Finset α) (a : α) (ha : a ∈ s)
    (f : ℕ → ℂ) :
    (∑ B : BlockContaining s a, f B.1.card) =
      ∑ k ∈ Finset.range s.card,
        (Nat.choose (s.card - 1) k : ℂ) * f (k + 1) := by
  classical
  rw [← Equiv.sum_comp (blockContainingEquivPowerset s a ha).symm]
  rw [← Finset.sum_coe_sort (s.erase a).powerset]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ (s.erase a).card := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcard : (s.erase a).card = s.card - 1 := by
    rw [Finset.card_erase_of_mem ha]
  rw [Finset.sum_powersetCard]
  simp only [blockContainingEquivPowerset, Equiv.coe_fn_symm_mk]
  rw [hcard]

end Finpartition

namespace Combinatorics

open PowerSeries

/-- The exponential-generating-function normalization of a power-series coefficient. -/
def powerSeriesMomentCoeff (Z : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n Z

/-- The exponential-generating-function normalization of a formal-log coefficient. -/
noncomputable def powerSeriesCumulantCoeff (Z : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n (PowerSeries.logOf Z)

private theorem derivative_log_mul_one_add_X :
    d⁄dX ℂ (PowerSeries.log ℂ) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_mk, pow_succ]

private theorem derivative_logOf_mul {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX ℂ (PowerSeries.logOf Z) * Z = d⁄dX ℂ Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst (Z - 1))
    derivative_log_mul_one_add_X
  have hgeom' :
      (d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z = 1 := by
    simpa [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub] using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsub]
  have hderiv : d⁄dX ℂ (Z - 1) = d⁄dX ℂ Z := by simp
  rw [hderiv]
  calc
    ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * d⁄dX ℂ Z) * Z =
        ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z) * d⁄dX ℂ Z := by
          ring
    _ = d⁄dX ℂ Z := by rw [hgeom']; simp

private theorem powerSeriesMomentCoeff_succ_recurrence {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) (n : ℕ) :
    powerSeriesMomentCoeff Z (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
  have hcoeff := congrArg (PowerSeries.coeff n) (derivative_logOf_mul hZ)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_derivative,
    PowerSeries.coeff_derivative] at hcoeff
  calc
    powerSeriesMomentCoeff Z (n + 1) =
        (n.factorial : ℂ) * (PowerSeries.coeff (n + 1) Z * (n + 1 : ℂ)) := by
          simp [powerSeriesMomentCoeff, Nat.factorial_succ]
          ring
    _ = (n.factorial : ℂ) *
        (∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff (p.1 + 1) (PowerSeries.logOf Z) * (p.1 + 1 : ℂ) *
            PowerSeries.coeff p.2 Z) := by rw [hcoeff]
    _ = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * powerSeriesCumulantCoeff Z (k + 1) *
          powerSeriesMomentCoeff Z (n - k) := by
      rw [Finset.mul_sum, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hnat := Nat.choose_mul_factorial_mul_factorial hkn
      have hfac :
          (n.factorial : ℂ) * (k + 1 : ℂ) =
            (Nat.choose n k : ℂ) * ((k + 1).factorial : ℂ) *
              ((n - k).factorial : ℂ) := by
        norm_cast
        calc
          n.factorial * (k + 1) = (k + 1) * n.factorial := by ac_rfl
          _ = (k + 1) * (Nat.choose n k * k.factorial * (n - k).factorial) := by
            rw [hnat]
          _ = Nat.choose n k * (k + 1).factorial * (n - k).factorial := by
            rw [Nat.factorial_succ]
            ac_rfl
      simp only [powerSeriesMomentCoeff, powerSeriesCumulantCoeff]
      rw [← hfac]
      ring

private theorem momentFromCumulant_powerSeriesCumulantCoeff
    {α : Type*} [DecidableEq α] {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) (s : Finset α) :
    Finpartition.momentFromCumulant
        (fun T : Finset α => powerSeriesCumulantCoeff Z T.card) s =
      powerSeriesMomentCoeff Z s.card := by
  classical
  induction s using Finset.strongInductionOn with
  | h s ih =>
      by_cases hs : s = ∅
      · subst s
        simp [Finpartition.momentFromCumulant, Finpartition.partitionProduct,
          powerSeriesMomentCoeff, hZ]
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        rw [Finpartition.momentFromCumulant_eq_sum_blockContaining _ ha]
        simp_rw [ih (s \ (· : Finset α)) (Finset.sdiff_ssubset ha)]
        let n := s.card - 1
        have hcard : s.card = n + 1 := by
          dsimp [n]
          omega
        rw [Finpartition.sum_blockContaining_card s a ha]
        subst hcard
        simpa [Finset.card_sdiff, n] using
          (powerSeriesMomentCoeff_succ_recurrence hZ n).symm

/-- Factorial-normalized coefficients of `logOf Z` are the finite-set cumulants of the
factorial-normalized coefficients of `Z`. -/
theorem factorial_mul_coeff_logOf_eq_cumulantFromMoment
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z = 1)
    {α : Type*} [DecidableEq α] {s : Finset α} (hs : s ≠ ∅) :
    (s.card.factorial : ℂ) * PowerSeries.coeff s.card (PowerSeries.logOf Z) =
      Finpartition.cumulantFromMoment
        (fun T : Finset α =>
          (T.card.factorial : ℂ) * PowerSeries.coeff T.card Z) s := by
  let κ : Finset α → ℂ := fun T => powerSeriesCumulantCoeff Z T.card
  have hm :
      (fun T : Finset α => powerSeriesMomentCoeff Z T.card) =
        Finpartition.momentFromCumulant κ := by
    funext T
    exact (momentFromCumulant_powerSeriesCumulantCoeff hZ T).symm
  change powerSeriesCumulantCoeff Z s.card = _
  change _ = Finpartition.cumulantFromMoment
    (fun T : Finset α => powerSeriesMomentCoeff Z T.card) s
  rw [hm]
  exact (Finpartition.cumulantFromMoment_momentFromCumulant κ hs).symm

/-- Cardinality-indexed form of the formal-log/finite-set-cumulant bridge. -/
theorem factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z = 1)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) * PowerSeries.coeff n (PowerSeries.logOf Z) =
      Finpartition.cumulantFromMoment
        (fun S : Finset (Fin n) =>
          (S.card.factorial : ℂ) * PowerSeries.coeff S.card Z)
        Finset.univ := by
  simpa using
    (factorial_mul_coeff_logOf_eq_cumulantFromMoment hZ
      (s := (Finset.univ : Finset (Fin n))) (by simpa using hn))

end Combinatorics
