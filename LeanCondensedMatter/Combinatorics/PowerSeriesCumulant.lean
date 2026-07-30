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

private noncomputable instance blockContainingFintype (s : Finset α) (a : α) :
    Fintype (BlockContaining s a) := by
  classical
  let f : BlockContaining s a → {T : Finset α // T ∈ s.powerset} :=
    fun B => ⟨B.1, Finset.mem_powerset.mpr B.2.1⟩
  exact Fintype.ofInjective f (by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun T : {T : Finset α // T ∈ s.powerset} => T.1) h)

private def blockContainingEquivPowerset (s : Finset α) (a : α) (ha : a ∈ s) :
    BlockContaining s a ≃ {T : Finset α // T ∈ (s.erase a).powerset} where
  toFun B := ⟨B.1.erase a, by
    rw [Finset.mem_powerset]
    intro x hx
    have hxB : x ∈ B.1 := Finset.mem_of_mem_erase hx
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
    have haT : a ∉ T.1 := by
      intro haT
      have hmem := (Finset.mem_powerset.mp T.2) haT
      exact (Finset.mem_erase.mp hmem).1 rfl
    simp [haT]

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
      (Finset.sdiff_union_of_subset hBsub)).avoid B = Q := by
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
    Finpartition s ≃ Σ B : BlockContaining s a, Finpartition (s \ B.1) where
  toFun P := ⟨⟨P.part a, P.part_subset a, P.mem_part ha⟩, P.avoid (P.part a)⟩
  invFun x := x.2.extend (Finset.ne_empty_of_mem x.1.2.2) disjoint_sdiff_self_left
    (Finset.sdiff_union_of_subset x.1.2.1)
  left_inv P := by
    apply Finpartition.ext
    change insert (P.part a) (P.avoid (P.part a)).parts = P.parts
    exact insert_part_parts_avoid P ha
  right_inv x := by
    rcases x with ⟨B, Q⟩
    let P := Q.extend (Finset.ne_empty_of_mem B.2.2) disjoint_sdiff_self_left
      (Finset.sdiff_union_of_subset B.2.1)
    have hBmem : B.1 ∈ P.parts := by
      exact Finset.mem_insert_self _ _
    have hpart : P.part a = B.1 := P.part_eq_of_mem hBmem B.2.2
    have hblock :
        (⟨P.part a, P.part_subset a, P.mem_part ha⟩ : BlockContaining s a) = B := by
      apply Subtype.ext
      exact hpart
    apply Sigma.ext hblock
    rw [hpart]
    exact heq_of_eq (avoid_extend_eq B.2.1 B.2.2 Q)

private theorem partitionProduct_partComplementEquiv_symm
    (κ : Finset α → ℂ) {s : Finset α} {a : α} (ha : a ∈ s)
    (x : Σ B : BlockContaining s a, Finpartition (s \ B.1)) :
    partitionProduct κ ((partComplementEquiv s a ha).symm x) =
      κ x.1.1 * partitionProduct κ x.2 := by
  classical
  rcases x with ⟨B, Q⟩
  change (∏ C ∈ insert B.1 Q.parts, κ C) =
    κ B.1 * ∏ C ∈ Q.parts, κ C
  rw [Finset.prod_insert]
  intro hB
  have haDiff : a ∈ s \ B.1 := Q.le hB B.2.2
  exact (Finset.mem_sdiff.mp haDiff).2 B.2.2

/-- The moment sum splits by the block containing a distinguished element. -/
private theorem momentFromCumulant_eq_sum_blockContaining (κ : Finset α → ℂ)
    {s : Finset α} {a : α} (ha : a ∈ s) :
    momentFromCumulant κ s =
      ∑ B : BlockContaining s a,
        κ B.1 * momentFromCumulant κ (s \ B.1) := by
  classical
  rw [momentFromCumulant, ← Equiv.sum_comp (partComplementEquiv s a ha).symm,
    Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro B
  simp_rw [partitionProduct_partComplementEquiv_symm κ ha]
  rw [← Finset.mul_sum]
  rfl

set_option linter.unusedDecidableInType false in
private theorem sum_blockContaining_card (s : Finset α) (a : α) (ha : a ∈ s)
    (f : ℕ → ℂ) :
    (∑ B : BlockContaining s a, f B.1.card) =
      ∑ k ∈ Finset.range s.card,
        (Nat.choose (s.card - 1) k : ℂ) * f (k + 1) := by
  classical
  rw [← Equiv.sum_comp (blockContainingEquivPowerset s a ha).symm]
  change (∑ T : {T : Finset α // T ∈ (s.erase a).powerset},
      f (insert a T.1).card) = _
  rw [← Finset.sum_subtype (s.erase a).powerset (fun _ => Iff.rfl)
    (fun T => f (insert a T).card)]
  have hcard : (s.erase a).card + 1 = s.card := Finset.card_erase_add_one ha
  rw [Finset.sum_powerset, hcard]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ T ∈ (s.erase a).powersetCard k, f (insert a T).card) =
        ∑ T ∈ (s.erase a).powersetCard k, f (k + 1) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTa : a ∉ T := by
        intro hTa
        have hsub := (Finset.mem_powersetCard.mp hT).1 hTa
        exact (Finset.mem_erase.mp hsub).1 rfl
      have hTk : T.card = k := (Finset.mem_powersetCard.mp hT).2
      rw [Finset.card_insert_of_notMem hTa, hTk]
    _ = (Nat.choose (s.card - 1) k : ℂ) * f (k + 1) := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      have herase : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      rw [herase]
      simp [nsmul_eq_mul]

end Finpartition

namespace Combinatorics

open PowerSeries

/-- The exponential-generating-function normalization of a power-series coefficient. -/
noncomputable def powerSeriesMomentCoeff (Z : PowerSeries ℂ) (n : ℕ) : ℂ :=
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
  have hone : (1 : PowerSeries ℂ).subst (Z - 1) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hgeom' :
      (d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z = 1 := by
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub, hone] at hgeom
    simpa using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℂ hsub]
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
  rw [PowerSeries.coeff_mul] at hcoeff
  simp_rw [PowerSeries.coeff_derivative] at hcoeff
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
      rw [Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      calc
        (n.factorial : ℂ) *
            (PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) * (k + 1 : ℂ) *
              PowerSeries.coeff (n - k) Z) =
            ((n.factorial : ℂ) * (k + 1 : ℂ)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by ring
        _ = ((Nat.choose n k : ℂ) * ((k + 1).factorial : ℂ) *
              ((n - k).factorial : ℂ)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by rw [hfac]
        _ = (Nat.choose n k : ℂ) *
              (((k + 1).factorial : ℂ) *
                PowerSeries.coeff (k + 1) (PowerSeries.logOf Z)) *
              (((n - k).factorial : ℂ) * PowerSeries.coeff (n - k) Z) := by ring

private theorem momentFromCumulant_powerSeriesCumulantCoeff
    {α : Type*} [DecidableEq α] {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) (s : Finset α) :
    Finpartition.momentFromCumulant
        (fun T : Finset α => powerSeriesCumulantCoeff Z T.card) s =
      powerSeriesMomentCoeff Z s.card := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    have hunique (P : Finpartition (∅ : Finset α)) : P = ⊥ := by
      apply Finpartition.ext
      have hparts : P.parts = ∅ := by
        ext B
        constructor
        · intro hB
          exact (P.ne_bot hB (Finset.subset_empty.mp (P.subset hB))).elim
        · intro hB
          simp at hB
      simpa [hparts]
    letI : Unique (Finpartition (∅ : Finset α)) :=
      { default := ⊥, uniq := hunique }
    have hdefault : (default : Finpartition (∅ : Finset α)) = ⊥ := hunique _
    simp [Finpartition.momentFromCumulant, Finpartition.partitionProduct,
      powerSeriesMomentCoeff, hZ, hdefault]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    rw [Finpartition.momentFromCumulant_eq_sum_blockContaining _ ha]
    have hsmall : ∀ B : Finpartition.BlockContaining s a,
        Finpartition.momentFromCumulant
            (fun T : Finset α => powerSeriesCumulantCoeff Z T.card) (s \ B.1) =
          powerSeriesMomentCoeff Z (s \ B.1).card := by
      intro B
      exact ih (s \ B.1) (Finset.sdiff_ssubset B.2.1 ⟨a, B.2.2⟩)
    simp_rw [hsmall]
    let n := s.card - 1
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
    have hcard : s.card = n + 1 := by
      dsimp [n]
      omega
    calc
      (∑ B : Finpartition.BlockContaining s a,
          powerSeriesCumulantCoeff Z B.1.card *
            powerSeriesMomentCoeff Z (s \ B.1).card) =
          ∑ B : Finpartition.BlockContaining s a,
            powerSeriesCumulantCoeff Z B.1.card *
              powerSeriesMomentCoeff Z (s.card - B.1.card) := by
        apply Fintype.sum_congr
        intro B
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr B.2.1]
      _ = ∑ k ∈ Finset.range s.card,
          (Nat.choose (s.card - 1) k : ℂ) *
            (powerSeriesCumulantCoeff Z (k + 1) *
              powerSeriesMomentCoeff Z (s.card - (k + 1))) := by
        exact Finpartition.sum_blockContaining_card s a ha
          (fun j => powerSeriesCumulantCoeff Z j *
            powerSeriesMomentCoeff Z (s.card - j))
      _ = powerSeriesMomentCoeff Z s.card := by
        rw [hcard]
        simpa [Nat.succ_eq_add_one, mul_assoc] using
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
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    intro h
    have hx : (⟨0, hnpos⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_univ _
    rw [h] at hx
    simpa using hx
  simpa using
    (factorial_mul_coeff_logOf_eq_cumulantFromMoment hZ
      (s := (Finset.univ : Finset (Fin n))) huniv)

end Combinatorics
