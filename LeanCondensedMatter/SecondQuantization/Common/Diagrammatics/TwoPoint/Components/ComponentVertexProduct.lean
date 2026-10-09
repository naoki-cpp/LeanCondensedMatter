import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition

set_option linter.style.header false

/-!
# Vertex products over external and vacuum components of two-point diagrams

The interaction vertices of a two-point diagram decompose into the interaction parts of its full
external-plus-interaction components. Reindexing finite products along that decomposition gives a
general vertex-weight factorization used by the fermionic amplitude layer.
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
      ∏ B : d.vertexGraph.componentPartition.parts,
        ∏ v : ↥(interactionSector
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, interactionSector_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) :=
  prod_eq_prod_interactionSectors d.vertexGraph (fun v => w (d.vertexLabel v))

end Common
end SecondQuantization
