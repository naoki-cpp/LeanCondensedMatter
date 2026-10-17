import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffle
import LeanCondensedMatter.Combinatorics.FiniteSumModEq
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic
import Mathlib.Tactic.Ring

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

/-- For distinct blocks, the two opposite inter-block inversion counts add up
to the total number of pairs of slots between the blocks. -/
theorem FamilySlotShuffleTo.blockInversionCount_add_swap
    {size : ι → ℕ} {total : ℕ} (shuffle : FamilySlotShuffleTo size total)
    (i j : ι) (hij : i ≠ j) :
    shuffle.blockInversionCount i j + shuffle.blockInversionCount j i =
      size i * size j := by
  classical
  rw [shuffle.blockInversionCount_of_ne hij,
    shuffle.blockInversionCount_of_ne hij.symm]
  have hswap :
      (∑ p : Fin (size j), ∑ q : Fin (size i),
        if shuffle.slotEquiv ⟨i, q⟩ < shuffle.slotEquiv ⟨j, p⟩ then 1 else 0) =
        (∑ p : Fin (size i), ∑ q : Fin (size j),
          if shuffle.slotEquiv ⟨i, p⟩ < shuffle.slotEquiv ⟨j, q⟩ then 1 else 0) := by
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    _ = ∑ p : Fin (size i), ∑ q : Fin (size j),
          ((if shuffle.slotEquiv ⟨j, q⟩ < shuffle.slotEquiv ⟨i, p⟩ then 1 else 0) +
            (if shuffle.slotEquiv ⟨i, p⟩ < shuffle.slotEquiv ⟨j, q⟩ then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_add_distrib]
    _ = ∑ _p : Fin (size i), ∑ _q : Fin (size j), (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      have htag : (⟨i, p⟩ : Σ k, Fin (size k)) ≠ ⟨j, q⟩ := by
        intro h
        exact hij (congrArg Sigma.fst h)
      have hne : shuffle.slotEquiv ⟨i, p⟩ ≠ shuffle.slotEquiv ⟨j, q⟩ :=
        shuffle.slotEquiv.injective.ne htag
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simp [hlt, (asymm hlt)]
      · simp [hlt, (asymm hlt)]
    _ = size i * size j := by simp

/-- When every block has even size, the inter-block inversion parity is
independent of the arbitrary order used to list the blocks. -/
theorem FamilySlotShuffleTo.orderedBlockInversionCount_modEq_of_even_sizes
    [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (order₁ order₂ : ι ≃ Fin (Fintype.card ι))
    (heven : ∀ i, Even (size i)) :
    Nat.ModEq 2
      (shuffle.orderedBlockInversionCount order₁)
      (shuffle.orderedBlockInversionCount order₂) := by
  classical
  have hflip (i j : ι) (hij : i ≠ j) :
      Nat.ModEq 2 (shuffle.blockInversionCount i j)
        (shuffle.blockInversionCount j i) := by
    have hsum := shuffle.blockInversionCount_add_swap i j hij
    obtain ⟨r, hr⟩ := heven i
    have hprod : size i * size j = 2 * (r * size j) := by
      rw [hr]
      ring
    change shuffle.blockInversionCount i j % 2 =
      shuffle.blockInversionCount j i % 2
    omega
  unfold FamilySlotShuffleTo.orderedBlockInversionCount
  refine finset_sum_offDiag_modEq_of_pair_add_modEq 2 (Finset.univ : Finset ι)
    (fun i j => if order₁ i < order₁ j then shuffle.blockInversionCount i j else 0)
    (fun i j => if order₂ i < order₂ j then shuffle.blockInversionCount i j else 0)
    ?_
  intro i _ j _ hij
  rcases lt_or_gt_of_ne (order₁.injective.ne hij) with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne (order₂.injective.ne hij) with h₂ | h₂
  · simpa [h₁, h₂, (asymm h₁), (asymm h₂)] using
      (Nat.ModEq.refl (n := 2) (shuffle.blockInversionCount i j))
  · simpa [h₁, h₂, (asymm h₁), (asymm h₂)] using hflip i j hij
  · simpa [h₁, h₂, (asymm h₁), (asymm h₂)] using (hflip i j hij).symm
  · simpa [h₁, h₂, (asymm h₁), (asymm h₂)] using
      (Nat.ModEq.refl (n := 2) (shuffle.blockInversionCount j i))

end Combinatorics
