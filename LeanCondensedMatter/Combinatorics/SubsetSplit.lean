import Mathlib.Data.Finset.SDiff
import Mathlib.Logic.Equiv.Set

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
def subsetSumSdiffEquiv {S T : Finset α} (h : T ⊆ S) : ↥T ⊕ ↥(S \ T) ≃ ↥S :=
  (Equiv.sumCongr (Equiv.refl ↥T) (Equiv.setCongr (by
    ext x
    simp))).trans
    (Equiv.Set.sumDiffSubset (s := (T : Set α)) (t := (S : Set α)) (by
      simpa using h))

@[simp]
theorem subsetSumSdiffEquiv_inl_apply {S T : Finset α} (h : T ⊆ S) (x : ↥T) :
    subsetSumSdiffEquiv h (Sum.inl x) = ⟨x.1, h x.2⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem subsetSumSdiffEquiv_inl {S T : Finset α} (h : T ⊆ S) (x : ↥T) :
    (subsetSumSdiffEquiv h (Sum.inl x) : α) = (x : α) := by
  rfl

@[simp]
theorem subsetSumSdiffEquiv_inr_apply {S T : Finset α} (h : T ⊆ S) (x : ↥(S \ T)) :
    subsetSumSdiffEquiv h (Sum.inr x) =
      ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem subsetSumSdiffEquiv_inr {S T : Finset α} (h : T ⊆ S) (x : ↥(S \ T)) :
    (subsetSumSdiffEquiv h (Sum.inr x) : α) = (x : α) := by
  rfl

end Combinatorics
