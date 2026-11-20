import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
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
  toFun B := ⟨B.1.erase a,
    Finset.mem_powerset.mpr (Finset.erase_subset_erase a B.2.1)⟩
  invFun T := ⟨insert a T.1, by
    constructor
    · rw [Finset.insert_subset_iff]
      exact ⟨ha, (Finset.mem_powerset.mp T.2).trans (Finset.erase_subset _ _)⟩
    · exact Finset.mem_insert_self _ _⟩
  left_inv B := Subtype.ext (Finset.insert_erase B.2.2)
  right_inv T := Subtype.ext <| Finset.erase_insert <|
    fun h => Finset.notMem_erase a s ((Finset.mem_powerset.mp T.2) h)

private theorem insert_part_parts_avoid {s : Finset α} (P : Finpartition s) {a : α}
    (ha : a ∈ s) :
    insert (P.part a) (P.avoid (P.part a)).parts = P.parts := by
  classical
  have hp : P.part a ∈ P.parts := P.part_mem.mpr ha
  have hmap :
      (P.parts.erase (P.part a)).image (· \ P.part a) =
        P.parts.erase (P.part a) := by
    calc
      _ = (P.parts.erase (P.part a)).image id := by
        apply Finset.image_congr
        intro B hB
        exact (P.disjoint (Finset.mem_of_mem_erase hB) hp
          (Finset.ne_of_mem_erase hB)).sdiff_eq_left
      _ = _ := Finset.image_id
  change insert (P.part a) ((P.parts.image (· \ P.part a)).erase ∅) = P.parts
  rw [← Finset.insert_erase hp, Finset.image_insert, hmap]
  simp [hp]

private theorem avoid_extend_eq {s B : Finset α} {a : α}
    (hBsub : B ⊆ s) (haB : a ∈ B) (Q : Finpartition (s \ B)) :
    (Q.extend (Finset.ne_empty_of_mem haB) disjoint_sdiff_self_left
      (Finset.sdiff_union_of_subset hBsub)).avoid B = Q := by
  classical
  have hmap : Q.parts.image (· \ B) = Q.parts := by
    calc
      _ = Q.parts.image id := Finset.image_congr (fun D hD =>
        (disjoint_sdiff_self_left.mono_left (Q.le hD)).sdiff_eq_left)
      _ = _ := Finset.image_id
  apply Finpartition.ext
  change ((insert B Q.parts).image (· \ B)).erase ∅ = Q.parts
  simp [Finset.image_insert, hmap]

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
    have hpart : P.part a = B.1 :=
      P.part_eq_of_mem (Finset.mem_insert_self _ _) B.2.2
    apply Sigma.ext (Subtype.ext hpart)
    change HEq (P.avoid (P.part a)) Q
    rw [hpart]
    exact heq_of_eq (avoid_extend_eq B.2.1 B.2.2 Q)


private theorem card_parts_distinguishedBlockEquiv_symm
    {s : Finset α} {a : α} (ha : a ∈ s)
    (x : Σ B : BlockContaining s a, Finpartition (s \ B.1)) :
    ((distinguishedBlockEquiv s a ha).symm x).parts.card = x.2.parts.card + 1 := by
  rcases x with ⟨B, Q⟩
  change
    (Q.extend (Finset.ne_empty_of_mem B.2.2) disjoint_sdiff_self_left
      (Finset.sdiff_union_of_subset B.2.1)).parts.card = Q.parts.card + 1
  exact card_extend Q B.1 s

private def subtypeSigmaSndEquiv {ι : Type*} {β : ι → Type*}
    (q : (i : ι) → β i → Prop) :
    {x : Σ i, β i // q x.1 x.2} ≃ Σ i, {b : β i // q i b} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by
    rcases x with ⟨⟨i, b⟩, hb⟩
    rfl
  right_inv x := by
    rcases x with ⟨i, ⟨b, hb⟩⟩
    rfl

/-- Partitions of `s` with `k + 1` blocks are equivalent to a choice of the block containing
`a` together with a `k`-block partition of its complement. -/
def partsCardSuccEquiv
    {s : Finset α} {a : α} (ha : a ∈ s) (k : ℕ) :
    {P : Finpartition s // P.parts.card = k + 1} ≃
      Σ B : BlockContaining s a,
        {Q : Finpartition (s \ B.1) // Q.parts.card = k} := by
  let e := distinguishedBlockEquiv s a ha
  refine (Equiv.subtypeEquiv e ?_).trans
    (subtypeSigmaSndEquiv
      (fun B : BlockContaining s a => fun Q : Finpartition (s \ B.1) => Q.parts.card = k))
  intro P
  have hcard : P.parts.card = (e P).2.parts.card + 1 := by
    simpa [e] using card_parts_distinguishedBlockEquiv_symm ha (e P)
  omega

section Semiring

variable {R : Type*} [CommSemiring R]

omit [DecidableEq α] in
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
