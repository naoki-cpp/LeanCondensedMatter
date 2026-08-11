import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Decomposing a set partition at a distinguished block

A partition of a finite set with a distinguished element is equivalent to the block containing that
element together with a partition of its complement. These results are pure set-partition
combinatorics and support recurrence arguments such as the power-series/cumulant bridge.
-/

open scoped BigOperators

namespace Finpartition

variable {α : Type*} [DecidableEq α]

/-- A subset of `s` containing the distinguished element `a`. -/
def BlockContaining (s : Finset α) (a : α) :=
  {B : Finset α // B ⊆ s ∧ a ∈ B}

noncomputable instance blockContainingFintype (s : Finset α) (a : α) :
    Fintype (BlockContaining s a) := by
  classical
  let f : BlockContaining s a → {T : Finset α // T ∈ s.powerset} :=
    fun B => ⟨B.1, Finset.mem_powerset.mpr B.2.1⟩
  exact Fintype.ofInjective f (by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun T : {T : Finset α // T ∈ s.powerset} => T.1) h)

/-- Blocks containing `a` correspond to subsets of `s.erase a`. -/
def blockContainingEquivPowerset (s : Finset α) (a : α) (ha : a ∈ s) :
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
def distinguishedBlockEquiv (s : Finset α) (a : α) (ha : a ∈ s) :
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
    change HEq (P.avoid (P.part a)) Q
    rw [hpart]
    exact heq_of_eq (avoid_extend_eq B.2.1 B.2.2 Q)

section Semiring

variable {R : Type*} [CommSemiring R]

private theorem partitionProduct_distinguishedBlockEquiv_symm
    (κ : Finset α → R) {s : Finset α} {a : α} (ha : a ∈ s)
    (x : Σ B : BlockContaining s a, Finpartition (s \ B.1)) :
    partitionProduct κ ((distinguishedBlockEquiv s a ha).symm x) =
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
theorem momentFromCumulant_eq_sum_blockContaining (κ : Finset α → R)
    {s : Finset α} {a : α} (ha : a ∈ s) :
    momentFromCumulant κ s =
      ∑ B : BlockContaining s a,
        κ B.1 * momentFromCumulant κ (s \ B.1) := by
  classical
  rw [momentFromCumulant, ← Equiv.sum_comp (distinguishedBlockEquiv s a ha).symm,
    Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro B
  simp_rw [partitionProduct_distinguishedBlockEquiv_symm κ ha]
  rw [← Finset.mul_sum]
  rfl

set_option linter.unusedDecidableInType false in
/-- Reindex a cardinality-dependent sum over distinguished blocks by their size. -/
theorem sum_blockContaining_card (s : Finset α) (a : α) (ha : a ∈ s)
    (f : ℕ → R) :
    (∑ B : BlockContaining s a, f B.1.card) =
      ∑ k ∈ Finset.range s.card,
        (Nat.choose (s.card - 1) k : R) * f (k + 1) := by
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
    _ = (Nat.choose (s.card - 1) k : R) * f (k + 1) := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      have herase : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      rw [herase]
      simp [nsmul_eq_mul]

end Semiring

end Finpartition
