import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Finite partitions induced by setoids

This module packages the finite-partition API used when connected components are represented by a
setoid on an ambient finite set.  It keeps the partition construction independent of any particular
graph representation: diagram-specific code only has to identify the setoid relation with the
relevant notion of reachability.
-/

namespace Setoid

variable {α : Type*} [DecidableEq α]

open Classical in
/-- The finite partition of `s` induced by the equivalence classes of `r`. -/
noncomputable def finpartitionOn (r : Setoid α) (s : Finset α) : Finpartition s :=
  Finpartition.ofSetSetoid r s

/-- The part of `finpartitionOn r s` containing `a`. -/
noncomputable def blockOn (r : Setoid α) (s : Finset α) (a : α) : Finset α :=
  (r.finpartitionOn s).part a

/-- Membership in a setoid block is membership in the support together with the setoid relation. -/
theorem mem_blockOn_iff (r : Setoid α) (s : Finset α) (a b : α) :
    b ∈ r.blockOn s a ↔ a ∈ s ∧ b ∈ s ∧ r a b := by
  classical
  simpa [Setoid.blockOn, Setoid.finpartitionOn] using
    (Finpartition.mem_part_ofSetSetoid_iff_rel (s := r) s (a := a) (b := b))

/-- Every supported point belongs to its own setoid block. -/
@[simp]
theorem self_mem_blockOn (r : Setoid α) (s : Finset α) {a : α} (ha : a ∈ s) :
    a ∈ r.blockOn s a :=
  (r.mem_blockOn_iff s a a).2 ⟨ha, ha, r.refl a⟩

/-- The block of a supported point is a part of the induced finite partition. -/
theorem blockOn_mem_parts (r : Setoid α) (s : Finset α) {a : α} (ha : a ∈ s) :
    r.blockOn s a ∈ (r.finpartitionOn s).parts := by
  change (r.finpartitionOn s).part a ∈ (r.finpartitionOn s).parts
  exact (r.finpartitionOn s).part_mem.2 ha

/-- Supported points have the same setoid block exactly when they are related. -/
theorem blockOn_eq_iff_rel (r : Setoid α) (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    r.blockOn s a = r.blockOn s b ↔ r a b := by
  constructor
  · intro h
    have hab : a ∈ r.blockOn s b := by
      rw [← h]
      exact r.self_mem_blockOn s ha
    exact r.symm' ((r.mem_blockOn_iff s b a).1 hab).2.2
  · intro hab
    change (r.finpartitionOn s).part a = (r.finpartitionOn s).part b
    exact ((r.finpartitionOn s).mem_part_iff_part_eq_part ha hb).1
      ((r.mem_blockOn_iff s b a).2 ⟨hb, ha, r.symm' hab⟩)

/-- Blocks of two non-related supported points are disjoint. -/
theorem blockOn_disjoint_of_not_rel (r : Setoid α) (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (h : ¬ r a b) :
    Disjoint (r.blockOn s a) (r.blockOn s b) :=
  (r.finpartitionOn s).disjoint
    (r.blockOn_mem_parts s ha)
    (r.blockOn_mem_parts s hb)
    (fun hEq => h ((r.blockOn_eq_iff_rel s ha hb).1 hEq))

/-- Every part of a setoid-induced finite partition is the block of a supported point. -/
theorem exists_blockOn_eq_of_mem (r : Setoid α) (s : Finset α)
    {B : Finset α} (hB : B ∈ (r.finpartitionOn s).parts) :
    ∃ a : α, a ∈ s ∧ r.blockOn s a = B := by
  obtain ⟨a, haB⟩ := (r.finpartitionOn s).nonempty_of_mem_parts hB
  have ha : a ∈ s := (r.finpartitionOn s).le hB haB
  refine ⟨a, ha, ?_⟩
  change (r.finpartitionOn s).part a = B
  exact (r.finpartitionOn s).part_eq_of_mem hB haB

/-- A setoid block equals a given partition part exactly when its base point lies in that part. -/
theorem blockOn_eq_iff_mem (r : Setoid α) (s : Finset α)
    {B : Finset α} (hB : B ∈ (r.finpartitionOn s).parts) (a : α) :
    r.blockOn s a = B ↔ a ∈ B := by
  change (r.finpartitionOn s).part a = B ↔ a ∈ B
  exact (r.finpartitionOn s).part_eq_iff_mem hB

end Setoid
