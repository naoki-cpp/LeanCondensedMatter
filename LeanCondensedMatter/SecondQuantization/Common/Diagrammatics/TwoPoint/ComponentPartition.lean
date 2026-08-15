import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Diagram
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Connected-component partitions of two-point diagrams

This module partitions the full vertex graph of a two-point diagram, including its two distinguished
external vertices. A component is a vacuum component exactly when it contains neither external
vertex. The main theorem identifies `HasNoVacuumComponent` with emptiness of the finite set of
vacuum component parts.

The full component partition is the canonical finite partition induced by Mathlib's
`SimpleGraph.reachableSetoid`; diagram-facing component blocks are views of its parts.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

open Classical in
/-- The partition of the full external-plus-interaction vertex set into graph components. -/
noncomputable def TwoPointDiagram.componentPartition {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Finpartition (Finset.univ : Finset (TwoPointVertex S)) :=
  Finpartition.ofSetoid d.vertexGraph.reachableSetoid

/-- The full two-point component containing `v`. -/
noncomputable def TwoPointDiagram.componentBlock {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (v : TwoPointVertex S) :
    Finset (TwoPointVertex S) :=
  d.componentPartition.part v

/-- Membership in a two-point component block is graph reachability. -/
theorem TwoPointDiagram.mem_componentBlock {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v w : TwoPointVertex S) :
    w ∈ d.componentBlock v ↔ d.vertexGraph.Reachable w v := by
  classical
  change w ∈ (Finpartition.ofSetoid d.vertexGraph.reachableSetoid).part v ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact d.vertexGraph.reachable_comm

@[simp]
theorem TwoPointDiagram.self_mem_componentBlock {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (v : TwoPointVertex S) :
    v ∈ d.componentBlock v :=
  (d.mem_componentBlock v v).2 (SimpleGraph.Reachable.refl _)

/-- Every component block occurs as a part of the component partition. -/
theorem TwoPointDiagram.componentBlock_mem_componentPartition {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (v : TwoPointVertex S) :
    d.componentBlock v ∈ d.componentPartition.parts := by
  change d.componentPartition.part v ∈ d.componentPartition.parts
  exact d.componentPartition.part_mem.2 (Finset.mem_univ v)

/-- Reachable vertices determine the same component block. -/
theorem TwoPointDiagram.componentBlock_eq_of_reachable {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) {v w : TwoPointVertex S}
    (h : d.vertexGraph.Reachable v w) :
    d.componentBlock v = d.componentBlock w := by
  change d.componentPartition.part v = d.componentPartition.part w
  exact (d.componentPartition.mem_part_iff_part_eq_part
    (Finset.mem_univ v) (Finset.mem_univ w)).1 ((d.mem_componentBlock w v).2 h)

/-- Two component blocks are equal exactly when their base vertices are reachable. -/
theorem TwoPointDiagram.componentBlock_eq_iff_reachable {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (v w : TwoPointVertex S) :
    d.componentBlock v = d.componentBlock w ↔ d.vertexGraph.Reachable v w := by
  constructor
  · intro h
    apply (d.mem_componentBlock w v).1
    rw [← h]
    exact d.self_mem_componentBlock v
  · exact d.componentBlock_eq_of_reachable

/-- A vertex belongs to a component part exactly when its component block is that part. -/
theorem TwoPointDiagram.componentBlock_eq_iff_mem {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {B : Finset (TwoPointVertex S)} (hB : B ∈ d.componentPartition.parts)
    (v : TwoPointVertex S) :
    d.componentBlock v = B ↔ v ∈ B := by
  change d.componentPartition.part v = B ↔ v ∈ B
  exact d.componentPartition.part_eq_iff_mem hB

/-- A component part contains at least one of the two external vertices. -/
def TwoPointDiagram.ComponentMeetsExternal {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) : Prop :=
  ∃ e : Fin 2, (Sum.inl e : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S))

/-- A component part is a vacuum component when it contains neither external vertex. -/
def TwoPointDiagram.ComponentIsVacuum {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) : Prop :=
  ¬ d.ComponentMeetsExternal B

/-- The component containing external vertex `e`. -/
noncomputable def TwoPointDiagram.externalComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    Finset (TwoPointVertex S) :=
  d.componentBlock (Sum.inl e)

/-- A component part meets the external sector exactly when it is one of the two external
components. -/
theorem TwoPointDiagram.componentMeetsExternal_iff_eq_externalComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    d.ComponentMeetsExternal B ↔
      ∃ e : Fin 2, (B : Finset (TwoPointVertex S)) = d.externalComponent e := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have hblock := (d.componentBlock_eq_iff_mem B.2 (Sum.inl e)).2 he
    simpa only [TwoPointDiagram.externalComponent] using hblock.symm
  · rintro ⟨e, hB⟩
    refine ⟨e, ?_⟩
    rw [hB]
    exact d.self_mem_componentBlock (Sum.inl e)

/-- `HasNoVacuumComponent` means precisely that every component-partition part meets the external
sector. -/
theorem TwoPointDiagram.hasNoVacuumComponent_iff_forall_component_meetsExternal
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.HasNoVacuumComponent ↔
      ∀ B : d.componentPartition.parts, d.ComponentMeetsExternal B := by
  constructor
  · intro h B
    obtain ⟨v, -, hv⟩ := d.componentPartition.part_surjOn B.2
    cases v with
    | inl e =>
        refine ⟨e, ?_⟩
        rw [← hv]
        exact d.self_mem_componentBlock (Sum.inl e)
    | inr v =>
        obtain ⟨e, he⟩ := h v
        refine ⟨e, ?_⟩
        rw [← hv]
        exact (d.mem_componentBlock (Sum.inr v) (Sum.inl e)).2 he
  · intro h v
    let B : d.componentPartition.parts :=
      ⟨d.componentBlock (Sum.inr v), d.componentBlock_mem_componentPartition (Sum.inr v)⟩
    obtain ⟨e, he⟩ := h B
    exact ⟨e, (d.mem_componentBlock (Sum.inr v) (Sum.inl e)).1 he⟩

open Classical in
/-- The finite set of component parts containing neither external vertex. -/
noncomputable def TwoPointDiagram.vacuumComponentParts {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Finset d.componentPartition.parts :=
  Finset.univ.filter d.ComponentIsVacuum

@[simp]
theorem TwoPointDiagram.mem_vacuumComponentParts {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    B ∈ d.vacuumComponentParts ↔ d.ComponentIsVacuum B := by
  simp [TwoPointDiagram.vacuumComponentParts]

/-- A two-point diagram has no vacuum component exactly when its finite set of vacuum component
parts is empty. -/
theorem TwoPointDiagram.hasNoVacuumComponent_iff_vacuumComponentParts_eq_empty
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.HasNoVacuumComponent ↔ d.vacuumComponentParts = ∅ := by
  rw [d.hasNoVacuumComponent_iff_forall_component_meetsExternal]
  constructor
  · intro h
    ext B
    simp [TwoPointDiagram.vacuumComponentParts, TwoPointDiagram.ComponentIsVacuum, h B]
  · intro h B
    by_contra hB
    have hmem : B ∈ d.vacuumComponentParts :=
      (d.mem_vacuumComponentParts B).2 hB
    simpa [h] using hmem

/-- The two external vertices are connected exactly when their component blocks agree. -/
theorem TwoPointDiagram.externalVerticesConnected_iff_externalComponent_eq {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.ExternalVerticesConnected ↔ d.externalComponent 0 = d.externalComponent 1 := by
  change d.vertexGraph.Reachable
      (Sum.inl (0 : Fin 2) : TwoPointVertex S) (Sum.inl (1 : Fin 2)) ↔ _
  exact (d.componentBlock_eq_iff_reachable
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).symm

/-- External connectedness is equivalent to absence of vacuum parts together with equality of the
two external component blocks. -/
theorem TwoPointDiagram.isExternallyConnected_iff {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.IsExternallyConnected ↔
      d.vacuumComponentParts = ∅ ∧ d.externalComponent 0 = d.externalComponent 1 := by
  rw [TwoPointDiagram.IsExternallyConnected,
    d.hasNoVacuumComponent_iff_vacuumComponentParts_eq_empty,
    d.externalVerticesConnected_iff_externalComponent_eq]

end Common
end SecondQuantization
