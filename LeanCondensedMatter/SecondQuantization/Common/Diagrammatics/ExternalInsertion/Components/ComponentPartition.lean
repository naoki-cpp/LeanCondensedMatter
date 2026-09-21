import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition

set_option linter.style.header false

/-!
# External-supported and vacuum components

This module classifies connected components of a finite external-insertion diagram according to
whether they meet the external sector. Unlike the two-point case, several distinct components may
meet external insertions, so vacuum-freeness is kept separate from any all-external-connected
condition.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- Every interaction vertex belongs to a component containing at least one external insertion. -/
def ExternalInsertionDiagram.HasNoVacuumComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) : Prop :=
  ∀ v : ↥S, ∃ e : Fin (2 * E),
    d.vertexGraph.Reachable
      (Sum.inl e : ExternalInsertionVertex E S)
      (Sum.inr v)

/-- The partition of the full external-plus-interaction vertex set into graph components. -/
noncomputable def ExternalInsertionDiagram.componentPartition {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    Finpartition (Finset.univ : Finset (ExternalInsertionVertex E S)) :=
  d.vertexGraph.componentPartition

/-- The full component containing `v`. -/
noncomputable def ExternalInsertionDiagram.componentBlock {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (v : ExternalInsertionVertex E S) :
    Finset (ExternalInsertionVertex E S) :=
  d.componentPartition.part v

/-- A component part contains at least one external insertion. -/
def ExternalInsertionDiagram.ComponentMeetsExternal {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) : Prop :=
  ∃ e : Fin (2 * E),
    (Sum.inl e : ExternalInsertionVertex E S) ∈
      (B : Finset (ExternalInsertionVertex E S))

open Classical in
/-- The external insertions contained in a full external-plus-interaction component part. -/
noncomputable def ExternalInsertionDiagram.externalPart {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) : Finset (Fin (2 * E)) :=
  Finset.univ.filter fun e =>
    (Sum.inl e : ExternalInsertionVertex E S) ∈ B

/-- Membership in the external part is membership of the corresponding external vertex in the full
component part. -/
@[simp]
theorem ExternalInsertionDiagram.mem_externalPart {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) (e : Fin (2 * E)) :
    e ∈ ExternalInsertionDiagram.externalPart B ↔
      (Sum.inl e : ExternalInsertionVertex E S) ∈ B := by
  classical
  simp [ExternalInsertionDiagram.externalPart]

/-- A component meets the external sector exactly when its extracted external part is nonempty. -/
theorem ExternalInsertionDiagram.componentMeetsExternal_iff_externalPart_nonempty
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    d.ComponentMeetsExternal B ↔
      (ExternalInsertionDiagram.externalPart
        (B : Finset (ExternalInsertionVertex E S))).Nonempty := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, (ExternalInsertionDiagram.mem_externalPart
      (B : Finset (ExternalInsertionVertex E S)) e).2 he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, (ExternalInsertionDiagram.mem_externalPart
      (B : Finset (ExternalInsertionVertex E S)) e).1 he⟩

/-- A component part is a vacuum component when it contains no external insertion. -/
def ExternalInsertionDiagram.ComponentIsVacuum {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) : Prop :=
  ¬ d.ComponentMeetsExternal B

/-- The component containing external insertion `e`. -/
noncomputable def ExternalInsertionDiagram.externalComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (e : Fin (2 * E)) :
    Finset (ExternalInsertionVertex E S) :=
  d.componentBlock (Sum.inl e)

/-- A component part meets the external sector exactly when it is the component of some external
insertion. -/
theorem ExternalInsertionDiagram.componentMeetsExternal_iff_eq_externalComponent
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    d.ComponentMeetsExternal B ↔
      ∃ e : Fin (2 * E),
        (B : Finset (ExternalInsertionVertex E S)) = d.externalComponent e := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have hB :
        (B : Finset (ExternalInsertionVertex E S)) ∈
          d.vertexGraph.componentPartition.parts := by
      simpa only [ExternalInsertionDiagram.componentPartition] using B.2
    have hblock :
        d.vertexGraph.componentBlock (Sum.inl e) =
          (B : Finset (ExternalInsertionVertex E S)) :=
      (d.vertexGraph.componentBlock_eq_iff_mem hB (Sum.inl e)).2 he
    simpa only [ExternalInsertionDiagram.externalComponent,
      ExternalInsertionDiagram.componentBlock,
      ExternalInsertionDiagram.componentPartition,
      SimpleGraph.componentBlock] using hblock.symm
  · rintro ⟨e, hB⟩
    refine ⟨e, ?_⟩
    rw [hB]
    change (Sum.inl e : ExternalInsertionVertex E S) ∈
      d.vertexGraph.componentBlock (Sum.inl e)
    exact d.vertexGraph.self_mem_componentBlock (Sum.inl e)

/-- Vacuum-freeness is equivalent to every connected component meeting the external sector. -/
theorem ExternalInsertionDiagram.hasNoVacuumComponent_iff_forall_component_meetsExternal
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.HasNoVacuumComponent ↔
      ∀ B : d.componentPartition.parts, d.ComponentMeetsExternal B := by
  constructor
  · intro h B
    obtain ⟨v, -, hv⟩ := d.componentPartition.part_surjOn B.2
    cases v with
    | inl e =>
        refine ⟨e, ?_⟩
        rw [← hv]
        change (Sum.inl e : ExternalInsertionVertex E S) ∈
          d.vertexGraph.componentBlock (Sum.inl e)
        exact d.vertexGraph.self_mem_componentBlock (Sum.inl e)
    | inr v =>
        obtain ⟨e, he⟩ := h v
        refine ⟨e, ?_⟩
        rw [← hv]
        change (Sum.inl e : ExternalInsertionVertex E S) ∈
          d.vertexGraph.componentBlock (Sum.inr v)
        exact (d.vertexGraph.mem_componentBlock (Sum.inr v) (Sum.inl e)).2 he
  · intro h v
    let B : d.componentPartition.parts :=
      ⟨d.componentBlock (Sum.inr v), by
        unfold ExternalInsertionDiagram.componentBlock
        exact d.componentPartition.part_mem.2 (Finset.mem_univ _)⟩
    obtain ⟨e, he⟩ := h B
    refine ⟨e, ?_⟩
    change (Sum.inl e : ExternalInsertionVertex E S) ∈
      d.vertexGraph.componentBlock (Sum.inr v) at he
    exact (d.vertexGraph.mem_componentBlock (Sum.inr v) (Sum.inl e)).1 he

open Classical in
/-- The finite set of component parts meeting at least one external insertion. -/
noncomputable def ExternalInsertionDiagram.externallySupportedComponentParts
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    Finset d.componentPartition.parts :=
  Finset.univ.filter d.ComponentMeetsExternal

@[simp]
theorem ExternalInsertionDiagram.mem_externallySupportedComponentParts
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    B ∈ d.externallySupportedComponentParts ↔ d.ComponentMeetsExternal B := by
  simp [ExternalInsertionDiagram.externallySupportedComponentParts]

open Classical in
/-- The finite set of component parts containing no external insertion. -/
noncomputable def ExternalInsertionDiagram.vacuumComponentParts
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    Finset d.componentPartition.parts :=
  Finset.univ.filter d.ComponentIsVacuum

@[simp]
theorem ExternalInsertionDiagram.mem_vacuumComponentParts
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    B ∈ d.vacuumComponentParts ↔ d.ComponentIsVacuum B := by
  simp [ExternalInsertionDiagram.vacuumComponentParts]

/-- Every connected component is either externally supported or vacuum. -/
theorem ExternalInsertionDiagram.univ_componentParts_eq_supported_union_vacuum
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    (Finset.univ : Finset d.componentPartition.parts) =
      d.externallySupportedComponentParts ∪ d.vacuumComponentParts := by
  classical
  ext B
  by_cases h : d.ComponentMeetsExternal B <;>
    simp [ExternalInsertionDiagram.ComponentIsVacuum, h]

/-- Externally supported and vacuum components are disjoint. -/
theorem ExternalInsertionDiagram.externallySupportedComponentParts_disjoint_vacuumComponentParts
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    Disjoint d.externallySupportedComponentParts d.vacuumComponentParts := by
  classical
  rw [Finset.disjoint_left]
  intro B hSupported hVacuum
  exact ((d.mem_vacuumComponentParts B).1 hVacuum)
    ((d.mem_externallySupportedComponentParts B).1 hSupported)

/-- A diagram has no vacuum component exactly when the finite set of vacuum component parts is
empty. -/
theorem ExternalInsertionDiagram.hasNoVacuumComponent_iff_vacuumComponentParts_eq_empty
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.HasNoVacuumComponent ↔ d.vacuumComponentParts = ∅ := by
  rw [d.hasNoVacuumComponent_iff_forall_component_meetsExternal]
  constructor
  · intro h
    ext B
    simp [ExternalInsertionDiagram.vacuumComponentParts,
      ExternalInsertionDiagram.ComponentIsVacuum, h B]
  · intro h B
    by_contra hB
    have hmem : B ∈ d.vacuumComponentParts :=
      (d.mem_vacuumComponentParts B).2 hB
    simpa [h] using hmem

end Common
end SecondQuantization
