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
  · by_contra hDisconnected
    let B : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inl (0 : Fin 2)),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl (0 : Fin 2))⟩
    have hExternalSector :
        Finset.toLeft (B : Finset (ExternalInsertionVertex 1 S)) =
          {(0 : Fin 2)} := by
      ext x
      fin_cases x
      · simp [B, Finset.mem_toLeft, d.vertexGraph.self_mem_componentBlock]
      · simp only [Finset.mem_toLeft, Finset.mem_singleton]
        constructor
        · intro hx
          apply hDisconnected
          exact ((d.vertexGraph.mem_componentBlock
            (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).1 hx).symm
        · intro hx
          exact False.elim (by simp at hx)
    have hEven := d.externalSector_card_even B
    rw [hExternalSector] at hEven
    simp at hEven

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
