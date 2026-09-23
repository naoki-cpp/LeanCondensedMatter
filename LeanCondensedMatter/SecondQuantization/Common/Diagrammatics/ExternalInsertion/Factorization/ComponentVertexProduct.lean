import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction

set_option linter.style.header false

/-!
# Interaction-vertex products over external-insertion components

The ambient quartic interaction vertices are the dependent disjoint union of the interaction
sectors of all full external-plus-interaction connected components. This module uses that
decomposition to factor arbitrary commutative interaction-vertex weights and the Dyson sign.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The restricted interaction-vertex label is the ambient label transported through the canonical
component interaction-sector decomposition. -/
@[simp]
theorem ExternalInsertionDiagram.restrictComponent_vertexLabel_interactionSectorComponentEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) :
    (d.restrictComponent B).vertexLabel v =
      d.vertexLabel (interactionSectorComponentEquiv d.vertexGraph.symm ⟨B, v⟩) := by
  apply congrArg d.vertexLabel
  apply Subtype.ext
  rfl

/-- A commutative product of interaction-vertex-local weights factors over all connected
components, including components with an empty interaction sector. -/
theorem ExternalInsertionDiagram.vertexWeight_eq_prod_components
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (w : InternalLabel → M) :
    d.vertexWeight w =
      ∏ B : d.vertexGraph.componentPartition.parts,
        (d.restrictComponent B).vertexWeight w := by
  classical
  unfold ExternalInsertionDiagram.vertexWeight
  calc
    (∏ v : ↥S, w (d.vertexLabel v)) =
        ∏ B : d.vertexGraph.componentPartition.parts,
          ∏ v : ↥(interactionSector
            (B : Finset (ExternalInsertionVertex E S))),
            w (d.vertexLabel (interactionSectorComponentEquiv d.vertexGraph.symm ⟨B, v⟩)) :=
      Fintype.prod_equiv_sigma interactionSectorComponentEquiv d.vertexGraph
        (fun v => w (d.vertexLabel v))
    _ = ∏ B : d.vertexGraph.componentPartition.parts,
          ∏ v : ↥(interactionSector
            (B : Finset (ExternalInsertionVertex E S))),
            w ((d.restrictComponent B).vertexLabel v) := by
      apply Fintype.prod_congr
      intro B
      apply Fintype.prod_congr
      intro v
      rw [d.restrictComponent_vertexLabel_interactionVertexComponentEquiv B v]

/-- The Dyson sign and interaction-vertex weight factor together over all connected components. -/
theorem ExternalInsertionDiagram.dysonSign_mul_vertexWeight_eq_prod_components
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (w : InternalLabel → ℂ) :
    (-1 : ℂ) ^ S.card * d.vertexWeight w =
      ∏ B : d.vertexGraph.componentPartition.parts,
        ((-1 : ℂ) ^ (interactionSector
          (B : Finset (ExternalInsertionVertex E S))).card *
          (d.restrictComponent B).vertexWeight w) := by
  classical
  have hsign :
      (-1 : ℂ) ^ S.card =
        ∏ B : d.vertexGraph.componentPartition.parts,
          (-1 : ℂ) ^ (interactionSector
            (B : Finset (ExternalInsertionVertex E S))).card := by
    rw [← d.sum_componentInteractionSector_card_eq,
      ← Finset.prod_pow_eq_pow_sum]
  rw [hsign, d.vertexWeight_eq_prod_components w, Finset.prod_mul_distrib]

end Common
end SecondQuantization
