import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Fin.Basic

set_option linter.style.header false

/-!
# Order-preserving shuffles of a finite family of slot blocks

`FamilySlotShuffleTo size total` interleaves one ordered block `Fin (size i)` for every index `i`
into `Fin total`, preserving the order inside each block.  The canonical `FamilySlotShuffle size`
specializes the ambient cardinality to `∑ i, size i` when the index type is finite.

This module contains only the pure finite combinatorics; shuffled integrands and continuity live in
`Analysis/OrderedSimplex/FamilyShuffleIntegrand.lean`.
-/

open scoped BigOperators

namespace Combinatorics

variable {ι : Type*}

/-- An order-preserving interleaving of a family of local slot blocks into `Fin total`. -/
structure FamilySlotShuffleTo (size : ι → ℕ) (total : ℕ) where
  /-- Equivalence between tagged local slots and ambient slots. -/
  slotEquiv : (Σ i : ι, Fin (size i)) ≃ Fin total
  strictMono : ∀ i, StrictMono (fun j => slotEquiv ⟨i, j⟩)

@[ext]
theorem FamilySlotShuffleTo.ext {size : ι → ℕ} {total : ℕ}
    {σ τ : FamilySlotShuffleTo size total}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Ambient family shuffles form a finite type when the block index type is finite. -/
noncomputable instance FamilySlotShuffleTo.instFintype [Fintype ι]
    (size : ι → ℕ) (total : ℕ) : Fintype (FamilySlotShuffleTo size total) := by
  classical
  exact Fintype.ofInjective (fun shuffle : FamilySlotShuffleTo size total => shuffle.slotEquiv)
    (fun _ _ h => FamilySlotShuffleTo.ext h)

/-- Transport only the ambient finite cardinality of a family shuffle. -/
noncomputable def FamilySlotShuffleTo.castTotalEquiv {size : ι → ℕ} {m n : ℕ} (h : m = n) :
    FamilySlotShuffleTo size m ≃ FamilySlotShuffleTo size n where
  toFun shuffle :=
    { slotEquiv := shuffle.slotEquiv.trans (Fin.castOrderIso h).toEquiv
      strictMono := by
        intro i a b hab
        exact (Fin.castOrderIso h).strictMono (shuffle.strictMono i hab) }
  invFun shuffle :=
    { slotEquiv := shuffle.slotEquiv.trans (Fin.castOrderIso h).symm.toEquiv
      strictMono := by
        intro i a b hab
        exact (Fin.castOrderIso h).symm.strictMono (shuffle.strictMono i hab) }
  left_inv shuffle := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    intro x
    change Fin.cast h.symm (Fin.cast h (shuffle.slotEquiv x)) = shuffle.slotEquiv x
    simp
  right_inv shuffle := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    intro x
    change Fin.cast h (Fin.cast h.symm (shuffle.slotEquiv x)) = shuffle.slotEquiv x
    simp

/-- A family shuffle whose ambient cardinality is exactly the sum of its local block sizes. -/
abbrev FamilySlotShuffle [Fintype ι] (size : ι → ℕ) :=
  FamilySlotShuffleTo size (∑ i, size i)

@[ext]
theorem FamilySlotShuffle.ext [Fintype ι] {size : ι → ℕ} {σ τ : FamilySlotShuffle size}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ :=
  FamilySlotShuffleTo.ext h

/-- The unique shuffle of an empty family of slot blocks. -/
noncomputable def FamilySlotShuffle.nil (size : Fin 0 → ℕ) : FamilySlotShuffle size where
  slotEquiv := Fintype.equivOfCardEq (by simp)
  strictMono := fun i => Fin.elim0 i

/-- A shuffle of an empty family is unique. -/
noncomputable instance FamilySlotShuffle.instUniqueZero (size : Fin 0 → ℕ) :
    Unique (FamilySlotShuffle size) where
  default := FamilySlotShuffle.nil size
  uniq shuffle := by
    apply FamilySlotShuffle.ext
    apply Equiv.ext
    rintro ⟨i, _⟩
    exact Fin.elim0 i

end Combinatorics
