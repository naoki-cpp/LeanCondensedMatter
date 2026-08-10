import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# The orbit partition of a permutation

A permutation of a finite type partitions it into orbits. Mathlib already supplies both halves of
this: `Equiv.Perm.SameCycle.setoid` is the orbit equivalence, and `Finpartition.ofSetoid` turns an
equivalence on a fintype into a partition of `univ`. This module names the composite and records the
membership characterization and the invariance of each block.

This is the first step towards reading `Matrix.det` as a moment whose connected pieces are the
permutations with a single orbit: the determinant sum ranges over all permutations, and grouping
them by this partition is the moment/cumulant decomposition.

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

/-- Two points lie in the same block exactly when the permutation moves one to the other. -/
theorem mem_part_orbitFinpartition_iff (σ : Perm α) [DecidableRel σ.SameCycle] (a b : α) :
    b ∈ (orbitFinpartition σ).part a ↔ σ.SameCycle a b :=
  Finpartition.mem_part_ofSetoid_iff_rel

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
