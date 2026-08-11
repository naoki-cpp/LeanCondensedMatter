import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Orbit partitions and cycle defect of a permutation

A permutation of a finite type partitions it into orbits. Mathlib already supplies both halves of
this: `Equiv.Perm.SameCycle.setoid` is the orbit equivalence, and `Finpartition.ofSetoid` turns an
equivalence on a fintype into a partition of `univ`. This module names the composite and records the
membership characterization and the invariance of each block.

The cycle defect

```text
Σ cycles C, (|C| - 1)
```

is the exponent used by the project's generic `ζ`-weighted permutation sum. Mathlib's `cycleType`
omits fixed-point 1-cycles, which contribute zero to this sum, so the native definition is
`cycleType.sum - cycleType.card`. The theorem `cycleDefect_eq_sum_orbitFinpartition` identifies this
with the same excess summed over the canonical orbit partition, including singleton fixed-point
orbits with zero contribution.

The decidability of `SameCycle` is taken as an instance argument, following Mathlib's own
`Equiv.Perm.cycleOf`. Any two choices agree, since `DecidableRel` is a subsingleton.
-/

namespace Combinatorics

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The partition of a finite type into the orbits of a permutation. -/
def orbitFinpartition (σ : Perm α) [DecidableRel σ.SameCycle] :
    Finpartition (univ : Finset α) :=
  Finpartition.ofSetoid (Equiv.Perm.SameCycle.setoid σ)

/-- The total cycle excess `Σ_C (|C| - 1)`. Fixed points contribute zero, so Mathlib's
nontrivial `cycleType` gives the equivalent formula `sum - card`. -/
def cycleDefect (σ : Perm α) : ℕ :=
  σ.cycleType.sum - σ.cycleType.card

private theorem cycleDefect_eq_sum_cycleFactorsFinset (σ : Perm α) :
    cycleDefect σ = ∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1) := by
  have hsum : (∑ c ∈ σ.cycleFactorsFinset, c.support.card) = σ.support.card := by
    rw [← Equiv.Perm.sum_cycleType σ, Equiv.Perm.cycleType_def]
    simp
  have hcard : σ.cycleType.card = σ.cycleFactorsFinset.card := by
    simp [Equiv.Perm.cycleType_def]
  have hpred : ∀ s : Finset (Perm α), s ⊆ σ.cycleFactorsFinset →
      (∑ c ∈ s, (c.support.card - 1)) =
        (∑ c ∈ s, c.support.card) - s.card := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        have hc_mem : c ∈ σ.cycleFactorsFinset := hs (by simp)
        have hc_cycle : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc_mem).1
        have hc_one : 1 ≤ c.support.card := (hc_cycle.two_le_card_support).trans' (by omega)
        have hs_sub : s ⊆ σ.cycleFactorsFinset := by
          intro d hd
          exact hs (by simp [hd])
        have ih' := ih hs_sub
        have hs_card_le : s.card ≤ ∑ d ∈ s, d.support.card := by
          calc
            s.card = ∑ _d ∈ s, 1 := by simp
            _ ≤ ∑ d ∈ s, d.support.card := by
              exact Finset.sum_le_sum fun d hd =>
                (Equiv.Perm.mem_cycleFactorsFinset_iff.1 (hs_sub hd)).1.two_le_card_support.trans' (by omega)
        simp only [Finset.sum_insert hc, Finset.card_insert_of_notMem hc]
        rw [ih']
        omega
  rw [cycleDefect, Equiv.Perm.sum_cycleType, hcard, ← hsum, ← hpred σ.cycleFactorsFinset]
  exact subset_rfl

/-- Two points lie in the same block exactly when the permutation moves one to the other. -/
theorem mem_part_orbitFinpartition_iff (σ : Perm α) [DecidableRel σ.SameCycle] (a b : α) :
    b ∈ (orbitFinpartition σ).part a ↔ σ.SameCycle a b :=
  Finpartition.mem_part_ofSetoid_iff_rel

private theorem support_cycleOf_eq_orbitPart (σ : Perm α) [DecidableRel σ.SameCycle]
    (x : α) (hx : x ∈ σ.support) :
    (σ.cycleOf x).support = (orbitFinpartition σ).part x := by
  ext y
  rw [Equiv.Perm.mem_support_cycleOf_iff' (Equiv.Perm.mem_support.mp hx),
    mem_part_orbitFinpartition_iff]

private noncomputable def orbitRepresentative (σ : Perm α) [DecidableRel σ.SameCycle]
    (B : (orbitFinpartition σ).parts) : α :=
  Classical.choose ((orbitFinpartition σ).nonempty_of_mem_parts B.2)

private theorem orbitRepresentative_mem (σ : Perm α) [DecidableRel σ.SameCycle]
    (B : (orbitFinpartition σ).parts) : orbitRepresentative σ B ∈ B.1 :=
  Classical.choose_spec ((orbitFinpartition σ).nonempty_of_mem_parts B.2)

private theorem orbitRepresentative_mem_support_of_one_lt_card
    (σ : Perm α) [DecidableRel σ.SameCycle]
    (B : (orbitFinpartition σ).parts) (hB : 1 < B.1.card) :
    orbitRepresentative σ B ∈ σ.support := by
  by_contra hnot
  have hfix : σ (orbitRepresentative σ B) = orbitRepresentative σ B := by
    simpa only [Equiv.Perm.mem_support, not_ne_iff] using hnot
  obtain ⟨y, hyB, hyne⟩ := B.1.exists_mem_ne hB (orbitRepresentative σ B)
  have hpart : (orbitFinpartition σ).part (orbitRepresentative σ B) = B.1 :=
    (orbitFinpartition σ).part_eq_of_mem B.2 (orbitRepresentative_mem σ B)
  have hsame : σ.SameCycle (orbitRepresentative σ B) y := by
    rw [← mem_part_orbitFinpartition_iff, hpart]
    exact hyB
  exact hyne (hsame.eq_of_left hfix).symm

/-- The cycle defect is the sum of `|B| - 1` over the canonical orbit blocks. Singleton fixed-point
orbits contribute zero. -/
theorem cycleDefect_eq_sum_orbitFinpartition (σ : Perm α) [DecidableRel σ.SameCycle] :
    cycleDefect σ = ∑ B ∈ (orbitFinpartition σ).parts, (B.card - 1) := by
  classical
  let P := orbitFinpartition σ
  let blocks := P.parts.filter fun B => 1 < B.card
  have hfilter :
      (∑ B ∈ blocks, (B.card - 1)) = ∑ B ∈ P.parts, (B.card - 1) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro B hBP hBnot
    have hBne : B.Nonempty := P.nonempty_of_mem_parts hBP
    have hBle : B.card ≤ 1 := Nat.le_of_not_gt (by simpa [blocks] using hBnot)
    have hBone : B.card = 1 := Nat.le_antisymm hBle hBne.one_le_card
    simp [hBone]
  have hbij :
      (∑ B ∈ blocks, (B.card - 1)) =
        ∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1) := by
    refine Finset.sum_bij
      (fun B hB =>
        σ.cycleOf (orbitRepresentative σ
          ⟨B, (Finset.mem_filter.mp (by simpa [blocks] using hB)).1⟩)) ?_ ?_ ?_ ?_
    · intro B hB
      have hmem : B ∈ P.parts := (Finset.mem_filter.mp (by simpa [blocks] using hB)).1
      have hcard : 1 < B.card := (Finset.mem_filter.mp (by simpa [blocks] using hB)).2
      exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2
        (orbitRepresentative_mem_support_of_one_lt_card σ ⟨B, hmem⟩ hcard)
    · intro B hB
      have hmem : B ∈ P.parts := (Finset.mem_filter.mp (by simpa [blocks] using hB)).1
      have hcard : 1 < B.card := (Finset.mem_filter.mp (by simpa [blocks] using hB)).2
      have hsupp := support_cycleOf_eq_orbitPart σ (orbitRepresentative σ ⟨B, hmem⟩)
        (orbitRepresentative_mem_support_of_one_lt_card σ ⟨B, hmem⟩ hcard)
      have hpart : P.part (orbitRepresentative σ ⟨B, hmem⟩) = B :=
        P.part_eq_of_mem hmem (orbitRepresentative_mem σ ⟨B, hmem⟩)
      simpa [P, hpart] using congrArg (fun s : Finset α => s.card - 1) hsupp.symm
    · intro B₁ B₂ hB₁ hB₂ heq
      have hmem₁ : B₁ ∈ P.parts := (Finset.mem_filter.mp (by simpa [blocks] using hB₁)).1
      have hmem₂ : B₂ ∈ P.parts := (Finset.mem_filter.mp (by simpa [blocks] using hB₂)).1
      have hcard₁ : 1 < B₁.card := (Finset.mem_filter.mp (by simpa [blocks] using hB₁)).2
      have hcard₂ : 1 < B₂.card := (Finset.mem_filter.mp (by simpa [blocks] using hB₂)).2
      have hsupp₁ := support_cycleOf_eq_orbitPart σ (orbitRepresentative σ ⟨B₁, hmem₁⟩)
        (orbitRepresentative_mem_support_of_one_lt_card σ ⟨B₁, hmem₁⟩ hcard₁)
      have hsupp₂ := support_cycleOf_eq_orbitPart σ (orbitRepresentative σ ⟨B₂, hmem₂⟩)
        (orbitRepresentative_mem_support_of_one_lt_card σ ⟨B₂, hmem₂⟩ hcard₂)
      have hpart₁ : P.part (orbitRepresentative σ ⟨B₁, hmem₁⟩) = B₁ :=
        P.part_eq_of_mem hmem₁ (orbitRepresentative_mem σ ⟨B₁, hmem₁⟩)
      have hpart₂ : P.part (orbitRepresentative σ ⟨B₂, hmem₂⟩) = B₂ :=
        P.part_eq_of_mem hmem₂ (orbitRepresentative_mem σ ⟨B₂, hmem₂⟩)
      have hs :
          (σ.cycleOf (orbitRepresentative σ ⟨B₁, hmem₁⟩)).support =
            (σ.cycleOf (orbitRepresentative σ ⟨B₂, hmem₂⟩)).support :=
        congrArg Equiv.Perm.support heq
      rw [hsupp₁, hsupp₂, hpart₁, hpart₂] at hs
      exact hs
    · intro c hc
      have hcCycle : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1
      obtain ⟨x, hx⟩ := hcCycle.nonempty_support
      have hxSupp : x ∈ σ.support := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx
      let B : Finset α := P.part x
      have hBmem : B ∈ P.parts := P.part_mem.2 (by simp [P])
      have hc_eq : c = σ.cycleOf x := Equiv.Perm.cycle_is_cycleOf hx hc
      have hsupport : c.support = B := by
        rw [hc_eq, support_cycleOf_eq_orbitPart σ x hxSupp]
        rfl
      have hBcard : 1 < B.card := by
        rw [← hsupport]
        exact hcCycle.one_lt_card_support
      have hBfilter : B ∈ blocks := by
        simp [blocks, hBmem, hBcard]
      refine ⟨B, hBfilter, ?_⟩
      have hrep : orbitRepresentative σ ⟨B, hBmem⟩ ∈ c.support := by
        rw [hsupport]
        exact orbitRepresentative_mem σ ⟨B, hBmem⟩
      exact Equiv.Perm.cycle_is_cycleOf hrep hc
  calc
    cycleDefect σ = ∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1) :=
      cycleDefect_eq_sum_cycleFactorsFinset σ
    _ = ∑ B ∈ blocks, (B.card - 1) := hbij.symm
    _ = ∑ B ∈ P.parts, (B.card - 1) := hfilter
    _ = ∑ B ∈ (orbitFinpartition σ).parts, (B.card - 1) := rfl

/-- A point lies in its own block. -/
theorem mem_part_orbitFinpartition_self (σ : Perm α) [DecidableRel σ.SameCycle] (a : α) :
    a ∈ (orbitFinpartition σ).part a :=
  (mem_part_orbitFinpartition_iff σ a a).2 (SameCycle.refl σ a)

/-- **Each block is invariant.** A permutation maps every orbit block into itself. -/
theorem apply_mem_part_orbitFinpartition (σ : Perm α) [DecidableRel σ.SameCycle] (a b : α)
    (hb : b ∈ (orbitFinpartition σ).part a) : σ b ∈ (orbitFinpartition σ).part a := by
  rw [mem_part_orbitFinpartition_iff] at hb ⊢
  exact hb.trans ⟨1, by simp⟩

/-- **Each block is invariant under the inverse.** -/
theorem symm_apply_mem_part_orbitFinpartition (σ : Perm α) [DecidableRel σ.SameCycle] (a b : α)
    (hb : b ∈ (orbitFinpartition σ).part a) : σ.symm b ∈ (orbitFinpartition σ).part a := by
  rw [mem_part_orbitFinpartition_iff] at hb ⊢
  exact hb.trans ⟨-1, by simp⟩

/-- The blocks of the identity permutation are singletons. -/
theorem mem_part_orbitFinpartition_one_iff [DecidableRel (1 : Perm α).SameCycle] (a b : α) :
    b ∈ (orbitFinpartition (1 : Perm α)).part a ↔ b = a := by
  rw [mem_part_orbitFinpartition_iff]
  constructor
  · intro h
    exact (sameCycle_one.1 h).symm
  · rintro rfl
    exact SameCycle.refl _ _

end Combinatorics
