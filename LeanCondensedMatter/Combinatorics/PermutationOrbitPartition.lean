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
omits fixed-point 1-cycles, which contribute zero to this sum, so the equivalent native formula
`cycleType.sum - cycleType.card` is the cheapest definition. The orbit-block form is proved at the
connected-decomposition layer where it is actually consumed.

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
