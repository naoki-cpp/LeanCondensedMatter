import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition

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
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
  classical
  calc
    (∏ v : ↥S, w (d.vertexLabel v)) =
        ∏ x : Σ B : d.componentPartition.parts,
          ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel (d.interactionVertexComponentEquiv.symm x)) :=
      (Equiv.prod_comp d.interactionVertexComponentEquiv.symm
        (fun v => w (d.vertexLabel v))).symm
    _ = ∏ B : d.componentPartition.parts,
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
      rw [Fintype.prod_sigma]
      rfl

/-- The Dyson sign factors into the external component sign and all vacuum-component signs. -/
theorem TwoPointDiagram.dysonSign_eq_external_mul_prod_vacuum
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (-1 : ℂ) ^ S.card =
      (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
        (d.externalComponent 0)).card *
        d.vacuumComponentParts.prod (fun B =>
          (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex S))).card) := by
  have h := d.prod_vertexLabel_eq_prod_componentInteractionParts (fun _ => (-1 : ℂ))
  rw [d.prod_componentParts_eq_external_mul_prod_vacuum] at h
  simpa [TwoPointDiagram.externalComponentPart, Finset.card_univ, Fintype.card_coe] using h

end Common
end SecondQuantization
