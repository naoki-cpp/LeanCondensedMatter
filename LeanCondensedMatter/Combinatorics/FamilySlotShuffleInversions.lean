import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import Mathlib.Algebra.BigOperators.ModEq

set_option linter.style.header false

/-!
# Inter-block inversion counts of finite-family shuffles

Block inversion counts record how distinct blocks interleave. An explicit block order selects
one orientation per pair of blocks for the total count. Modular agreement transports from each
block pair to that total. These counts are independent of permutation signs and pairing crossings.
-/

open scoped BigOperators

namespace Combinatorics

variable {ι : Type*}

/-- Number of ambient-order inversions in which a slot of a distinct block `j` occurs
before a slot of block `i`. The diagonal is zero, so this records only inter-block inversions.
The orientation is explicit so consumers can choose the block order supplied by their own semantics
rather than imposing an order on the family index type here. -/
noncomputable def FamilySlotShuffleTo.blockInversionCount {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (i j : ι) : ℕ := by
  classical
  exact if i = j then 0
    else
      ∑ p : Fin (size i), ∑ q : Fin (size j),
        if shuffle.slotEquiv ⟨j, q⟩ < shuffle.slotEquiv ⟨i, p⟩ then 1 else 0

@[simp]
theorem FamilySlotShuffleTo.blockInversionCount_self {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (i : ι) :
    shuffle.blockInversionCount i i = 0 := by
  classical
  simp [FamilySlotShuffleTo.blockInversionCount]

theorem FamilySlotShuffleTo.blockInversionCount_of_ne {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) {i j : ι} (hij : i ≠ j) :
    shuffle.blockInversionCount i j =
      ∑ p : Fin (size i), ∑ q : Fin (size j),
        if shuffle.slotEquiv ⟨j, q⟩ < shuffle.slotEquiv ⟨i, p⟩ then 1 else 0 := by
  classical
  simp [FamilySlotShuffleTo.blockInversionCount, hij]

/-- Total inter-block inversion count relative to an explicit ordering of the blocks.

The order selects exactly one orientation of every unordered pair of distinct blocks. Keeping that
choice explicit avoids imposing an arbitrary order on the family index type. -/
noncomputable def FamilySlotShuffleTo.orderedBlockInversionCount [Fintype ι]
    {size : ι → ℕ} {total : ℕ} (shuffle : FamilySlotShuffleTo size total)
    (blockOrder : ι ≃ Fin (Fintype.card ι)) : ℕ :=
  ∑ ij ∈ (Finset.univ : Finset ι).offDiag,
    if blockOrder ij.1 < blockOrder ij.2
    then shuffle.blockInversionCount ij.1 ij.2 else 0

/-- Pointwise modular agreement of inter-block inversion counts transports to the total ordered
inter-block inversion count for the same block order. -/
theorem FamilySlotShuffleTo.orderedBlockInversionCount_modEq_of_blockInversionCount_modEq
    [Fintype ι] {size₁ size₂ : ι → ℕ} {total₁ total₂ n : ℕ}
    (σ : FamilySlotShuffleTo size₁ total₁)
    (τ : FamilySlotShuffleTo size₂ total₂)
    (blockOrder : ι ≃ Fin (Fintype.card ι))
    (h : ∀ i j, i ≠ j →
      Nat.ModEq n (σ.blockInversionCount i j) (τ.blockInversionCount i j)) :
    Nat.ModEq n
      (σ.orderedBlockInversionCount blockOrder)
      (τ.orderedBlockInversionCount blockOrder) := by
  classical
  unfold FamilySlotShuffleTo.orderedBlockInversionCount
  refine Nat.ModEq.sum (n := n) ?_
  intro ij hij
  simp only [Finset.mem_offDiag] at hij
  by_cases hlt : blockOrder ij.1 < blockOrder ij.2
  · simp only [hlt, ite_eq_left]
    exact h ij.1 ij.2 hij.2.2
  · simp only [hlt, ite_false]
    exact Nat.ModEq.refl 0

end Combinatorics
