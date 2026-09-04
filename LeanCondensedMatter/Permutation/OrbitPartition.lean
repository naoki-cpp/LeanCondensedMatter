import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Orbit partitions and cycle defect of a permutation

A permutation of a finite type partitions it into orbits. Mathlib already supplies both halves of
this: `Equiv.Perm.SameCycle.setoid` is the orbit equivalence, and `Finpartition.ofSetoid` turns an
equivalence on a fintype into a partition of `univ`. This module names the composite and records the
canonical membership characterization.

The cycle defect

```text
Σ cycles C, (|C| - 1)
```

is the exponent used by the project's generic `ζ`-weighted permutation sum. Mathlib's `cycleType`
omits fixed-point 1-cycles, which contribute zero to this sum, so the native definition is
`cycleType.sum - cycleType.card`. The theorem `cycleDefect_eq_sum_orbitFinpartition` identifies this
with the same excess summed over the canonical orbit partition, including singleton fixed-point
orbits with zero contribution.

The decidability of `SameCycle` is taken as an instance argument by the structural partition API.
The cycle-factor comparison uses Mathlib's canonical decidability instance supplied by the finite
index type.
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
  have hpred :
      (∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1)) =
        (∑ c ∈ σ.cycleFactorsFinset, c.support.card) - σ.cycleFactorsFinset.card := by
    simpa using
      (Finset.sum_tsub_distrib σ.cycleFactorsFinset
        (f := fun c : Perm α => c.support.card) (g := fun _ => 1)
        (fun c hc =>
          (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1.two_le_card_support.trans' (by omega)))
  rw [cycleDefect, Equiv.Perm.sum_cycleType, hcard, ← hsum, ← hpred]

/-- Two points lie in the same block exactly when they are in the same permutation orbit. -/
theorem mem_part_orbitFinpartition_iff (σ : Perm α) [DecidableRel σ.SameCycle] (a b : α) :
    b ∈ (orbitFinpartition σ).part a ↔ σ.SameCycle a b :=
  Finpartition.mem_part_ofSetoid_iff_rel

private theorem support_cycleOf_eq_orbitPart (σ : Perm α)
    (x : α) (hx : x ∈ σ.support) :
    (σ.cycleOf x).support = (orbitFinpartition σ).part x := by
  ext y
  constructor
  · intro hy
    exact (mem_part_orbitFinpartition_iff σ x y).2
      ((Equiv.Perm.mem_support_cycleOf_iff' (Equiv.Perm.mem_support.mp hx)).1 hy)
  · intro hy
    exact (Equiv.Perm.mem_support_cycleOf_iff' (Equiv.Perm.mem_support.mp hx)).2
      ((mem_part_orbitFinpartition_iff σ x y).1 hy)

private noncomputable def orbitRepresentative (σ : Perm α)
    (B : (orbitFinpartition σ).parts) : α :=
  Classical.choose ((orbitFinpartition σ).nonempty_of_mem_parts B.2)

private theorem orbitRepresentative_mem (σ : Perm α)
    (B : (orbitFinpartition σ).parts) : orbitRepresentative σ B ∈ B.1 :=
  Classical.choose_spec ((orbitFinpartition σ).nonempty_of_mem_parts B.2)

private theorem orbitRepresentative_mem_support_of_one_lt_card
    (σ : Perm α) (B : (orbitFinpartition σ).parts) (hB : 1 < B.1.card) :
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

private noncomputable def orbitBlockCycle (σ : Perm α)
    (B : (orbitFinpartition σ).parts) : Perm α :=
  σ.cycleOf (orbitRepresentative σ B)

private theorem orbitBlockCycle_support_eq (σ : Perm α)
    (B : (orbitFinpartition σ).parts) (hB : 1 < B.1.card) :
    (orbitBlockCycle σ B).support = B.1 := by
  calc
    (orbitBlockCycle σ B).support =
        (orbitFinpartition σ).part (orbitRepresentative σ B) := by
      exact support_cycleOf_eq_orbitPart σ (orbitRepresentative σ B)
        (orbitRepresentative_mem_support_of_one_lt_card σ B hB)
    _ = B.1 := (orbitFinpartition σ).part_eq_of_mem B.2 (orbitRepresentative_mem σ B)

private theorem orbitBlockCycle_mem_cycleFactorsFinset
    (σ : Perm α) (B : (orbitFinpartition σ).parts) (hB : 1 < B.1.card) :
    orbitBlockCycle σ B ∈ σ.cycleFactorsFinset := by
  exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2
    (orbitRepresentative_mem_support_of_one_lt_card σ B hB)

/-- The cycle defect is the sum of `|B| - 1` over the canonical orbit blocks. Singleton fixed-point
orbits contribute zero. -/
theorem cycleDefect_eq_sum_orbitFinpartition (σ : Perm α) :
    cycleDefect σ = ∑ B ∈ (orbitFinpartition σ).parts, (B.card - 1) := by
  classical
  have hfilter :
      (∑ B ∈ (orbitFinpartition σ).parts.filter (fun B => 1 < B.card), (B.card - 1)) =
        ∑ B ∈ (orbitFinpartition σ).parts, (B.card - 1) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro B hBP hBnot
    have hnotlt : ¬ 1 < B.card := by
      intro hlt
      exact hBnot (Finset.mem_filter.mpr ⟨hBP, hlt⟩)
    have hBle : B.card ≤ 1 := Nat.le_of_not_gt hnotlt
    have hBne : B.Nonempty := (orbitFinpartition σ).nonempty_of_mem_parts hBP
    have hBone : B.card = 1 := Nat.le_antisymm hBle (Finset.one_le_card.mpr hBne)
    simp [hBone]
  have hbij :
      (∑ B ∈ (orbitFinpartition σ).parts.filter (fun B => 1 < B.card), (B.card - 1)) =
        ∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1) := by
    refine Finset.sum_bij
      (fun B hB => orbitBlockCycle σ ⟨B, (Finset.mem_filter.mp hB).1⟩) ?_ ?_ ?_ ?_
    · intro B hB
      exact orbitBlockCycle_mem_cycleFactorsFinset σ
        ⟨B, (Finset.mem_filter.mp hB).1⟩ (Finset.mem_filter.mp hB).2
    · intro B₁ hB₁ B₂ hB₂ heq
      have hs := congrArg Equiv.Perm.support heq
      rw [orbitBlockCycle_support_eq σ ⟨B₁, (Finset.mem_filter.mp hB₁).1⟩
          (Finset.mem_filter.mp hB₁).2,
        orbitBlockCycle_support_eq σ ⟨B₂, (Finset.mem_filter.mp hB₂).1⟩
          (Finset.mem_filter.mp hB₂).2] at hs
      exact hs
    · intro c hc
      have hcCycle : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1
      obtain ⟨x, hx⟩ := hcCycle.nonempty_support
      have hxSupp : x ∈ σ.support := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx
      have hBmem : (orbitFinpartition σ).part x ∈ (orbitFinpartition σ).parts :=
        (orbitFinpartition σ).part_mem.2 (by simp)
      have hc_eq : c = σ.cycleOf x := Equiv.Perm.cycle_is_cycleOf hx hc
      have hsupport : c.support = (orbitFinpartition σ).part x := by
        calc
          c.support = (σ.cycleOf x).support := congrArg Equiv.Perm.support hc_eq
          _ = (orbitFinpartition σ).part x := support_cycleOf_eq_orbitPart σ x hxSupp
      have hBcard : 1 < ((orbitFinpartition σ).part x).card := by
        have hc2 : 2 ≤ c.support.card := hcCycle.two_le_card_support
        rw [← hsupport]
        omega
      have hBfilter :
          (orbitFinpartition σ).part x ∈
            (orbitFinpartition σ).parts.filter (fun B => 1 < B.card) :=
        Finset.mem_filter.mpr ⟨hBmem, hBcard⟩
      refine ⟨(orbitFinpartition σ).part x, hBfilter, ?_⟩
      have hrep :
          orbitRepresentative σ ⟨(orbitFinpartition σ).part x, hBmem⟩ ∈ c.support := by
        rw [hsupport]
        exact orbitRepresentative_mem σ ⟨(orbitFinpartition σ).part x, hBmem⟩
      simpa [orbitBlockCycle] using (Equiv.Perm.cycle_is_cycleOf hrep hc).symm
    · intro B hB
      have hsupp := orbitBlockCycle_support_eq σ
        ⟨B, (Finset.mem_filter.mp hB).1⟩ (Finset.mem_filter.mp hB).2
      simpa using congrArg (fun s : Finset α => s.card - 1) hsupp.symm
  calc
    cycleDefect σ = ∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1) :=
      cycleDefect_eq_sum_cycleFactorsFinset σ
    _ = ∑ B ∈ (orbitFinpartition σ).parts.filter (fun B => 1 < B.card), (B.card - 1) :=
      hbij.symm
    _ = ∑ B ∈ (orbitFinpartition σ).parts, (B.card - 1) := hfilter

end Combinatorics
