import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction

set_option linter.style.header false

/-!
# Restricting vacuum components of external-insertion diagrams

This module extracts the interaction vertices belonging to a full external-plus-interaction
component and restricts the ambient pairing to its legs. For a vacuum component, no external leg is
present, so the restricted legs can be reindexed directly as the four local legs of an ordinary
quartic diagram.

The construction is statistics-independent. Partner-invariant pairing restriction is owned by
`Combinatorics.PerfectPairing.Restriction`; this module supplies the external-insertion component
predicate and the vacuum-specific leg reindexing.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

open Classical in
/-- The interaction vertices contained in a full external-plus-interaction component part. -/
noncomputable def ExternalInsertionDiagram.interactionPart {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) : Finset (Fin N) :=
  S.filter fun v =>
    ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : ExternalInsertionVertex E S) ∈ B

/-- Membership in the interaction part is membership of the corresponding interaction vertex in the
full component part. -/
theorem ExternalInsertionDiagram.mem_interactionPart {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) (v : Fin N) :
    v ∈ ExternalInsertionDiagram.interactionPart B ↔
      ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : ExternalInsertionVertex E S) ∈ B := by
  classical
  unfold ExternalInsertionDiagram.interactionPart
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose, h⟩

/-- Membership in the interaction part for a vertex already carrying its ambient-membership proof. -/
@[simp]
theorem ExternalInsertionDiagram.mem_interactionPart_subtype {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) (v : ↥S) :
    (v : Fin N) ∈ ExternalInsertionDiagram.interactionPart B ↔
      (Sum.inr v : ExternalInsertionVertex E S) ∈ B := by
  rw [ExternalInsertionDiagram.mem_interactionPart]
  constructor
  · rintro ⟨hv, h⟩
    have hvEq : (⟨(v : Fin N), hv⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h
  · intro h
    refine ⟨v.2, ?_⟩
    have hvEq : (⟨(v : Fin N), v.2⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h

/-- The interaction part of a full component is contained in the ambient interaction-vertex set. -/
theorem ExternalInsertionDiagram.interactionPart_subset {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) :
    ExternalInsertionDiagram.interactionPart B ⊆ S := by
  intro v hv
  obtain ⟨hvS, _⟩ := (ExternalInsertionDiagram.mem_interactionPart B v).1 hv
  exact hvS

/-- A flattened leg belongs to `B` when the component block of its incident vertex is `B`. -/
def ExternalInsertionDiagram.legInComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S))
    (leg : Fin (2 * (2 * S.card + E))) : Prop :=
  d.componentBlock (externalInsertionVertexOfLeg leg) = B

/-- For an actual component-partition part, a leg belongs to the component exactly when its incident
vertex belongs to that part. -/
theorem ExternalInsertionDiagram.legInComponent_iff_vertex_mem {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    {B : Finset (ExternalInsertionVertex E S)} (hB : B ∈ d.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔ externalInsertionVertexOfLeg leg ∈ B := by
  unfold ExternalInsertionDiagram.legInComponent ExternalInsertionDiagram.componentBlock
  apply d.vertexGraph.componentBlock_eq_iff_mem
  simpa only [ExternalInsertionDiagram.componentPartition] using hB

/-- Membership of an unflattened leg in a component part. -/
def ExternalInsertionDiagram.unflattenedLegInComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (leg : ExternalInsertionLeg E S) : Prop :=
  externalInsertionLegVertex leg ∈ (B : Finset (ExternalInsertionVertex E S))

/-- Flattening preserves the component-membership predicate. -/
theorem ExternalInsertionDiagram.legInComponent_iff_unflattened {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔
      d.unflattenedLegInComponent B (externalInsertionLegEquiv E S leg) := by
  rw [d.legInComponent_iff_vertex_mem B.2 leg]
  unfold ExternalInsertionDiagram.unflattenedLegInComponent
  rw [externalInsertionLegVertex_externalInsertionLegEquiv]

/-- Component-leg membership is invariant under the pairing partner permutation. -/
theorem ExternalInsertionDiagram.legInComponent_partner_iff {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S))
    (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔ d.legInComponent B (d.pairing.partner leg) := by
  unfold ExternalInsertionDiagram.legInComponent
  have hEq :
      d.componentBlock (externalInsertionVertexOfLeg leg) =
        d.componentBlock (externalInsertionVertexOfLeg (d.pairing.partner leg)) := by
    change d.vertexGraph.componentBlock (externalInsertionVertexOfLeg leg) =
      d.vertexGraph.componentBlock (externalInsertionVertexOfLeg (d.pairing.partner leg))
    exact d.vertexGraph.componentBlock_eq_of_reachable
      (d.pairing.vertexGraph_reachable_partner externalInsertionVertexOfLeg leg).symm
  rw [hEq]

/-- The partner permutation restricted to the legs of one full component. -/
noncomputable def ExternalInsertionDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S)) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg} :=
  d.pairing.partnerSubtypePerm (d.legInComponent B) fun leg =>
    d.legInComponent_partner_iff B leg

/-- The restricted partner has the same underlying flattened leg as the ambient partner. -/
theorem ExternalInsertionDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S))
    (leg : {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card + E))) = d.pairing.partner leg := by
  simpa only [ExternalInsertionDiagram.restrictedPartner] using
    d.pairing.partnerSubtypePerm_val (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff B i) leg

/-- For a vacuum part, unflattened component legs are exactly the four local legs of the extracted
interaction vertices. -/
noncomputable def ExternalInsertionDiagram.vacuumLegDataEquiv {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : ExternalInsertionLeg E S // d.unflattenedLegInComponent B leg} ≃
      ↥(ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        exact (⟨p.1.1,
          (ExternalInsertionDiagram.mem_interactionPart_subtype
            (B : Finset (ExternalInsertionVertex E S)) p.1).2 hleg⟩, p.2)
  invFun p :=
    let v : ↥S :=
      ⟨p.1.1, ExternalInsertionDiagram.interactionPart_subset
        (B : Finset (ExternalInsertionVertex E S)) p.1.2⟩
    ⟨Sum.inr (v, p.2), by
      change (Sum.inr v : ExternalInsertionVertex E S) ∈
        (B : Finset (ExternalInsertionVertex E S))
      exact (ExternalInsertionDiagram.mem_interactionPart_subtype
        (B : Finset (ExternalInsertionVertex E S)) v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv p := by
    rcases p with ⟨v, l⟩
    apply Prod.ext
    · exact Subtype.ext (by rfl)
    · rfl

/-- Reindex the legs of a vacuum component as the flattened legs of an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.vacuumBlockLegEquiv {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg} ≃
      Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))).card)) :=
  ((externalInsertionLegEquiv E S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened B leg).trans
    ((d.vacuumLegDataEquiv B hVac).trans
      (quarticLegEquiv (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S)))).symm)

/-- The perfect pairing induced on a vacuum component. -/
noncomputable def ExternalInsertionDiagram.restrictedVacuumPairing {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    Pairing (2 * (ExternalInsertionDiagram.interactionPart
      (B : Finset (ExternalInsertionVertex E S))).card) :=
  d.pairing.restrictAlongEquiv (d.legInComponent B)
    (fun leg => d.legInComponent_partner_iff (B : Finset (ExternalInsertionVertex E S)) leg)
    (d.vacuumBlockLegEquiv B hVac)

/-- The restricted vacuum pairing agrees with the ambient partner under the vacuum leg
reindexing. -/
theorem ExternalInsertionDiagram.restrictedVacuumPairing_partner_vacuumBlockLegEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (leg : {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg}) :
    (d.restrictedVacuumPairing B hVac).partner (d.vacuumBlockLegEquiv B hVac leg) =
      d.vacuumBlockLegEquiv B hVac
        (d.restrictedPartner (B : Finset (ExternalInsertionVertex E S)) leg) := by
  simpa only [ExternalInsertionDiagram.restrictedVacuumPairing,
    ExternalInsertionDiagram.restrictedPartner] using
    d.pairing.restrictAlongEquiv_partner (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) i)
      (d.vacuumBlockLegEquiv B hVac) leg

/-- Restrict a vacuum component of an external-insertion diagram to an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.restrictVacuumComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    QuarticDiagram InternalLabel N
      (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, ExternalInsertionDiagram.interactionPart_subset
      (B : Finset (ExternalInsertionVertex E S)) v.2⟩
  pairing := d.restrictedVacuumPairing B hVac

end Common
end SecondQuantization
