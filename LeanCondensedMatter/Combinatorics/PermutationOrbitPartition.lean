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
