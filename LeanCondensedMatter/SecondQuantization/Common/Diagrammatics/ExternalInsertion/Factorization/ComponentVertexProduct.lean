import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction

set_option linter.style.header false

/-!
# Interaction-vertex products over external-insertion components

The ambient quartic interaction vertices are the dependent disjoint union of the interaction
sectors of all full external-plus-interaction connected components. This module uses that
decomposition to factor arbitrary commutative interaction-vertex weights.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

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
  simpa only [ExternalInsertionDiagram.vertexWeight,
    ExternalInsertionDiagram.restrictComponent] using
    (prod_eq_prod_interactionSectors d.vertexGraph
      (fun v => w (d.vertexLabel v)))

end Common
end SecondQuantization
