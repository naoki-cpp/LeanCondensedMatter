import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct

set_option linter.style.header false

/-!
# Vertex products over external and vacuum components of two-point diagrams

The interaction vertices of a two-point diagram decompose into the interaction parts of its full
external-plus-interaction components. Reindexing finite products along that decomposition gives the
vertex-weight and Dyson-sign factorizations needed by the fermionic amplitude layer.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- A product of interaction-vertex-local weights factors over all full components. -/
theorem TwoPointDiagram.prod_vertexLabel_eq_prod_componentInteractionParts
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (w : InternalLabel → M) :
    (∏ v : ↥S, w (d.vertexLabel v)) =
      ∏ B : d.componentPartition.parts,
        ∏ v : ↥(interactionSector
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, interactionSector_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
  calc
    (∏ v : ↥S, w (d.vertexLabel v)) =
        ∏ B : d.componentPartition.parts,
          ∏ v : ↥(interactionSector
            (B : Finset (TwoPointVertex S))),
            w (d.vertexLabel (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) :=
      Fintype.prod_equiv_sigma d.interactionVertexComponentEquiv
        (fun v => w (d.vertexLabel v))
    _ = ∏ B : d.componentPartition.parts,
        ∏ v : ↥(interactionSector
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, interactionSector_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
      apply Fintype.prod_congr
      intro B
      apply Fintype.prod_congr
      intro v
      apply congrArg (fun x : ↥S => w (d.vertexLabel x))
      apply Subtype.ext
      exact d.interactionVertexComponentEquiv_symm_val ⟨B, v⟩

/-- The Dyson sign factors into the external component sign and all vacuum-component signs. -/
theorem TwoPointDiagram.dysonSign_eq_external_mul_prod_vacuum
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (-1 : ℂ) ^ S.card =
      (-1 : ℂ) ^ (interactionSector
        (d.externalComponent 0)).card *
        d.vacuumComponentParts.prod (fun B =>
          (-1 : ℂ) ^ (interactionSector
            (B : Finset (TwoPointVertex S))).card) := by
  have h := d.prod_vertexLabel_eq_prod_componentInteractionParts (fun _ => (-1 : ℂ))
  rw [d.prod_componentParts_eq_external_mul_prod_vacuum] at h
  have hext :
      (d.externalComponentPart : Finset (TwoPointVertex S)) = d.externalComponent 0 := rfl
  rw [hext] at h
  simpa [Finset.card_univ, Fintype.card_coe] using h

end Common
end SecondQuantization
