import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction

set_option linter.style.header false

/-!
# External connectivity with two external insertion legs

Each connected component of an external-insertion diagram has an even number
of one-legged external vertices. Consequently, when the whole diagram has
exactly two external vertices, they belong to the same component regardless
of the number of interaction vertices or vacuum components.

Combining this parity property with the generic external-component
characterization identifies vacuum-freeness with whole-graph preconnectedness
for two external insertions. The result is purely combinatorial and does not
identify the independent two-point and arbitrary-external diagram types.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- In a quartic diagram with exactly two one-legged external insertions,
the two external vertices necessarily lie in the same component.

This holds even if separate pure-vacuum components are present. -/
theorem ExternalInsertionDiagram.allExternalVerticesConnected_two
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel 1 N S) :
    AllExternalVerticesConnected d.vertexGraph := by
  apply (allExternalVerticesConnected_iff_reachable_anchor
    d.vertexGraph (0 : Fin 2)).2
  intro e
  fin_cases e
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.reachable_finTwo_of_even_left_components
      d.vertexGraph d.externalSector_card_even

/-- For exactly two external insertions, a diagram is fully connected
if and only if it has no vacuum component. This need not hold for four
or more external insertions. -/
theorem ExternalInsertionDiagram.preconnected_iff_hasNoVacuumComponent_two
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel 1 N S) :
    d.vertexGraph.Preconnected ↔ HasNoVacuumComponent d.vertexGraph := by
  rw [preconnected_iff_hasNoVacuumComponent_and_allExternalVerticesConnected]
  simp [d.allExternalVerticesConnected_two]

end Common
end SecondQuantization
