import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sigma

set_option linter.style.header false

/-!
# Order-preserving shuffles of a finite family of slot blocks

`FamilySlotShuffle size` interleaves one ordered block `Fin (size i)` for every finite index `i`
into `Fin (∑ i, size i)`, preserving the order inside each block.  This module contains only the
pure finite combinatorics; shuffled integrands and continuity live in
`Analysis/OrderedSimplex/FamilyShuffleIntegrand.lean`.
-/

open scoped BigOperators

namespace Combinatorics

variable {ι : Type*} [Fintype ι]

/-- An order-preserving interleaving of a finite family of local slot blocks. -/
structure FamilySlotShuffle (size : ι → ℕ) where
  /-- Equivalence between tagged local slots and ambient slots. -/
  slotEquiv : (Σ i : ι, Fin (size i)) ≃ Fin (∑ i, size i)
  strictMono : ∀ i, StrictMono (fun j => slotEquiv ⟨i, j⟩)

@[ext]
theorem FamilySlotShuffle.ext {size : ι → ℕ} {σ τ : FamilySlotShuffle size}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Finite-family shuffles form a finite type when the finite index type has decidable equality. -/
noncomputable instance FamilySlotShuffle.instFintype [DecidableEq ι] (size : ι → ℕ) :
    Fintype (FamilySlotShuffle size) :=
  Fintype.ofInjective (fun shuffle : FamilySlotShuffle size => shuffle.slotEquiv)
    (fun _ _ h => FamilySlotShuffle.ext h)

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
