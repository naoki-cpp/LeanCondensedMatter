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

/-- The external block of an insertion agrees with the external slots of its
ambient graph component. -/
theorem ExternalInsertionDiagram.externalComponentPartition_part_eq_toLeft_componentBlock
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (e : Fin (2 * E)) :
    (externalComponentPartition d.vertexGraph).part e =
      Finset.toLeft (d.vertexGraph.componentBlock (Sum.inl e)) := by
  classical
  ext b
  rw [mem_externalComponentPartition_part, Finset.mem_toLeft,
    d.vertexGraph.mem_componentBlock]
  exact d.vertexGraph.reachable_comm

/-- Every external component has an even number of one-legged insertions. -/
theorem ExternalInsertionDiagram.externalComponentPartition_part_card_even
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (e : Fin (2 * E)) :
    Even ((externalComponentPartition d.vertexGraph).part e).card := by
  rw [d.externalComponentPartition_part_eq_toLeft_componentBlock e]
  exact d.externalSector_card_even
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩

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
  exact d.externalComponentPartition_part_card_even e


/-- Every connected component with external support determines a block of
the induced partition of external insertions. -/
theorem ExternalInsertionDiagram.toLeft_mem_externalComponentPartition_parts
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (hB : B ∈ externallySupportedComponentParts d.vertexGraph) :
    (B : Finset (ExternalInsertionVertex E S)).toLeft ∈
      (externalComponentPartition d.vertexGraph).parts := by
  classical
  obtain ⟨e, hEq⟩ :=
    (componentMeetsExternal_iff_exists_eq_componentBlock d.vertexGraph B).mp
      ((mem_externallySupportedComponentParts d.vertexGraph B).mp hB)
  rw [hEq, ← d.externalComponentPartition_part_eq_toLeft_componentBlock e]
  exact (externalComponentPartition d.vertexGraph).part_mem.2 (Finset.mem_univ e)

/-- The full-graph connected components meeting external insertions correspond
bijectively to the blocks of the induced external partition.

The map forgets the internal vertices but loses no component information:
each supported component contains an external vertex, and each external block
comes from exactly one full-graph connected component. -/
noncomputable def ExternalInsertionDiagram.supportedComponentsEquivExternalBlocks
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    {B : d.vertexGraph.componentPartition.parts //
      B ∈ externallySupportedComponentParts d.vertexGraph} ≃
      (externalComponentPartition d.vertexGraph).parts := by
  classical
  let G := d.vertexGraph
  let π := externalComponentPartition G
  let toBlock :
      {B : G.componentPartition.parts // B ∈ externallySupportedComponentParts G} →
        π.parts := fun B =>
    ⟨(B.1.1 : Finset (ExternalInsertionVertex E S)).toLeft,
      d.toLeft_mem_externalComponentPartition_parts B.1 B.2⟩
  apply Equiv.ofBijective toBlock
  constructor
  · intro B C h
    have hLeft :
        (B.1.1 : Finset (ExternalInsertionVertex E S)).toLeft =
          (C.1.1 : Finset (ExternalInsertionVertex E S)).toLeft :=
      congrArg Subtype.val h
    obtain ⟨e, heB⟩ :=
      (mem_externallySupportedComponentParts G B.1).mp B.2
    have heC : (Sum.inl e : ExternalInsertionVertex E S) ∈
        (C.1.1 : Finset (ExternalInsertionVertex E S)) := by
      apply Finset.mem_toLeft.mp
      rw [← hLeft]
      exact Finset.mem_toLeft.mpr heB
    have hBeq : (B.1.1 : Finset (ExternalInsertionVertex E S)) =
        G.componentBlock (Sum.inl e) :=
      ((G.componentBlock_eq_iff_mem B.1.2 (Sum.inl e)).2 heB).symm
    have hCeq : (C.1.1 : Finset (ExternalInsertionVertex E S)) =
        G.componentBlock (Sum.inl e) :=
      ((G.componentBlock_eq_iff_mem C.1.2 (Sum.inl e)).2 heC).symm
    apply Subtype.ext
    apply Subtype.ext
    exact hBeq.trans hCeq.symm
  · intro P
    obtain ⟨e, -, he⟩ := π.part_surjOn P.2
    let B : G.componentPartition.parts :=
      ⟨G.componentBlock (Sum.inl e),
        G.componentBlock_mem_componentPartition (Sum.inl e)⟩
    have hB : B ∈ externallySupportedComponentParts G :=
      (mem_externallySupportedComponentParts G B).2
        ⟨e, G.self_mem_componentBlock (Sum.inl e)⟩
    refine ⟨⟨B, hB⟩, ?_⟩
    apply Subtype.ext
    change (G.componentBlock (Sum.inl e)).toLeft = (P : Finset (Fin (2 * E)))
    rw [← d.externalComponentPartition_part_eq_toLeft_componentBlock e]
    exact he

/-- The supported-component/external-block bijection sends a component to
precisely its external insertions (with their ambient labels and order). -/
@[simp]
theorem ExternalInsertionDiagram.supportedComponentsEquivExternalBlocks_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : {B : d.vertexGraph.componentPartition.parts //
      B ∈ externallySupportedComponentParts d.vertexGraph}) :
    ((d.supportedComponentsEquivExternalBlocks B : 
      (externalComponentPartition d.vertexGraph).parts) : Finset (Fin (2 * E))) =
      (B.1.1 : Finset (ExternalInsertionVertex E S)).toLeft := by
  rfl

end Common
end SecondQuantization
