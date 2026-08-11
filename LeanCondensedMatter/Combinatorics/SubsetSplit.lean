import Mathlib.Data.Finset.Sdiff
import Mathlib.Logic.Equiv.Basic

set_option linter.style.header false

/-!
# Splitting a finite set along a subset

A finite set splits as a subset together with its relative complement. This is the primitive behind
presenting the legs of a diagram as a two-part splitting indexed by *which vertices* are on each
side, before any diagram exists to read the sides off.

Stated for `Finset` subtypes rather than for `Equiv.sumCompl`, because the two sides have to be the
subtypes `↥T` and `↥(S \ T)` that the leg reindexings are already stated over.
-/

namespace Combinatorics

variable {α : Type*} [DecidableEq α]

/-- A finite set is its subset together with the relative complement. -/
def subsetSumSdiffEquiv {S T : Finset α} (h : T ⊆ S) : ↥T ⊕ ↥(S \ T) ≃ ↥S where
  toFun := Sum.elim (fun x => ⟨x.1, h x.2⟩) (fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩)
  invFun x :=
    if hx : (x : α) ∈ T then Sum.inl ⟨x, hx⟩
    else Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩ | ⟨x, hx⟩
    · simp [hx]
    · rw [Finset.mem_sdiff] at hx
      simp [hx.2]
  right_inv x := by
    by_cases hx : (x : α) ∈ T <;> simp [hx]

@[simp]
theorem subsetSumSdiffEquiv_inl {S T : Finset α} (h : T ⊆ S) (x : ↥T) :
    (subsetSumSdiffEquiv h (Sum.inl x) : α) = (x : α) :=
  rfl

@[simp]
theorem subsetSumSdiffEquiv_inr {S T : Finset α} (h : T ⊆ S) (x : ↥(S \ T)) :
    (subsetSumSdiffEquiv h (Sum.inr x) : α) = (x : α) :=
  rfl

end Combinatorics
