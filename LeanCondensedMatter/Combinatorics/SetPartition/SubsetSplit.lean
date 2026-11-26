import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false

/-!
# Splitting a finite set into subfinsets

A finite set splits as a subset together with its relative complement. This is the primitive behind
presenting the legs of a diagram as a two-part splitting indexed by *which vertices* are on each
side, before any diagram exists to read the sides off.

Stated for `Finset` subtypes rather than for `Equiv.sumCompl`, because the two sides have to be the
subtypes `↥T` and `↥(S \ T)` that the leg reindexings are already stated over.
-/

namespace Combinatorics

/-- A finite set is the dependent disjoint union of subfinsets classified by an owner map.
The fibers may be empty; each must contain exactly the elements with its specified owner. -/
noncomputable def equivSigmaSubfinsets {α ι : Type*}
    (t : Finset α) (owner : ↥t → ι) (fiber : ι → Finset α)
    (hfiber : ∀ i, fiber i ⊆ t)
    (hmem : ∀ (i : ι) (x : ↥t), (x : α) ∈ fiber i ↔ owner x = i) :
    ↥t ≃ Σ i, ↥(fiber i) :=
  (Equiv.sigmaFiberEquiv owner).symm.trans
    (Equiv.sigmaCongrRight fun i =>
      { toFun := fun x => ⟨x.1.1, (hmem i x.1).2 x.2⟩
        invFun := fun x => ⟨⟨x.1, hfiber i x.2⟩,
          (hmem i ⟨x.1, hfiber i x.2⟩).1 x.2⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl })

variable {α : Type*} [DecidableEq α]

/-- A finite set is its subset together with the relative complement. -/
def subsetSumSdiffEquiv {S T : Finset α} (h : T ⊆ S) : ↥T ⊕ ↥(S \ T) ≃ ↥S :=
  (Equiv.Finset.union T (S \ T)
    (disjoint_sdiff_self_right : Disjoint T (S \ T))).trans
    (Equiv.subtypeEquivProp (by
      simpa only [Finset.union_sdiff_of_subset h]))

@[simp]
theorem subsetSumSdiffEquiv_inl_apply {S T : Finset α} (h : T ⊆ S) (x : ↥T) :
    subsetSumSdiffEquiv h (Sum.inl x) = ⟨x.1, h x.2⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem subsetSumSdiffEquiv_inr_apply {S T : Finset α} (h : T ⊆ S) (x : ↥(S \ T)) :
    subsetSumSdiffEquiv h (Sum.inr x) =
      ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩ := by
  apply Subtype.ext
  rfl

end Combinatorics
