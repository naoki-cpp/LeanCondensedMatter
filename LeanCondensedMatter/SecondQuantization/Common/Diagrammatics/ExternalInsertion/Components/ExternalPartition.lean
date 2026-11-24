import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction

set_option linter.style.header false

/-!
# External-insertion connected-component partition

The reachable-component partition on external slots is the left-summand
restriction of the full vertex component partition. Every block has even
cardinality, since a closed connected component pairs all of its legs and
quartic internal vertices contribute four legs.

This partition provides the finite-set indexing for future source cumulants.
No external-order fermionic shuffle sign is absorbed into the partition itself.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- All blocks of the induced external partition have even cardinality. -/
theorem ExternalInsertionDiagram.externalComponentPartition_block_card_even
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (Fin (2 * E)))
    (hB : B ∈ (externalComponentPartition d.vertexGraph).parts) :
    Even B.card := by
  classical
  obtain ⟨e, -, he⟩ :=
    (externalComponentPartition d.vertexGraph).part_surjOn hB
  rw [← he]
  rw [externalComponentPartition_part_eq_toLeft_componentBlock d.vertexGraph e]
  exact d.externalSector_card_even
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩

end Common
end SecondQuantization
