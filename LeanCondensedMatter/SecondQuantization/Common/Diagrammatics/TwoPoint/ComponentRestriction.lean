import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction

set_option linter.style.header false

/-!
# Restricting components of two-point diagrams

This module extracts the interaction vertices belonging to a full external-plus-interaction
component and restricts the ambient pairing to its legs. For a vacuum component, those legs are
reindexed as the four local legs of an ordinary quartic diagram, producing the diagram needed for
vacuum-bubble factorization.

Partner-invariant pairing restriction is owned by `Combinatorics.PerfectPairing.Restriction`; this
module supplies the two-point component predicate and the vacuum-specific leg reindexing. Restriction
to the component containing the external legs and amplitude factorization are developed separately.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

open Classical in
/-- The interaction vertices contained in a full external-plus-interaction component part. -/
noncomputable def TwoPointDiagram.interactionPart {N : ℕ} {S : Finset (Fin N)}
    (B : Finset (TwoPointVertex S)) : Finset (Fin N) :=
  S.filter fun v =>
    ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : TwoPointVertex S) ∈ B

/-- Membership in the interaction part is membership of the corresponding interaction vertex in the
full component part. -/
theorem TwoPointDiagram.mem_interactionPart {N : ℕ} {S : Finset (Fin N)}
    (B : Finset (TwoPointVertex S)) (v : Fin N) :
    v ∈ TwoPointDiagram.interactionPart B ↔
      ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : TwoPointVertex S) ∈ B := by
  classical
  unfold TwoPointDiagram.interactionPart
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose, h⟩

/-- Membership in the interaction part for a vertex already carrying its ambient-membership proof. -/
@[simp]
theorem TwoPointDiagram.mem_interactionPart_subtype {N : ℕ} {S : Finset (Fin N)}
    (B : Finset (TwoPointVertex S)) (v : ↥S) :
    (v : Fin N) ∈ TwoPointDiagram.interactionPart B ↔
      (Sum.inr v : TwoPointVertex S) ∈ B := by
  rw [TwoPointDiagram.mem_interactionPart]
  constructor
  · rintro ⟨hv, h⟩
    have hvEq : (⟨(v : Fin N), hv⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h
  · intro h
    refine ⟨v.2, ?_⟩
    have hvEq : (⟨(v : Fin N), v.2⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h

/-- The interaction part of a full component is contained in the ambient interaction-vertex set. -/
theorem TwoPointDiagram.interactionPart_subset {N : ℕ} {S : Finset (Fin N)}
    (B : Finset (TwoPointVertex S)) :
    TwoPointDiagram.interactionPart B ⊆ S := by
  intro v hv
  obtain ⟨hvS, _⟩ := (TwoPointDiagram.mem_interactionPart B v).1 hv
  exact hvS

/-- The vertex incident to an unflattened two-point leg. -/
def twoPointLegVertex {S : Finset (Fin N)} : TwoPointLeg S → TwoPointVertex S
  | .inl e => .inl e
  | .inr p => .inr p.1

@[simp]
theorem twoPointLegVertex_external {S : Finset (Fin N)} (e : Fin 2) :
    twoPointLegVertex (Sum.inl e : TwoPointLeg S) = (Sum.inl e : TwoPointVertex S) :=
  rfl

@[simp]
theorem twoPointLegVertex_interaction {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    twoPointLegVertex (Sum.inr (v, l) : TwoPointLeg S) = (Sum.inr v : TwoPointVertex S) :=
  rfl

/-- A flattened leg belongs to `B` when the component block of its incident vertex is `B`. -/
def TwoPointDiagram.legInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : Fin (2 * (2 * S.card + 1))) : Prop :=
  d.componentBlock (twoPointVertexOfLeg leg) = B

/-- Flattened legs belonging to one full component of a two-point diagram. -/
abbrev TwoPointDiagram.ComponentLeg {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :=
  {leg : Fin (2 * (2 * S.card + 1)) //
    d.legInComponent (B : Finset (TwoPointVertex S)) leg}

/-- For an actual component-partition part, a leg belongs to the component exactly when its incident
vertex belongs to that part. -/
theorem TwoPointDiagram.legInComponent_iff_vertex_mem {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {B : Finset (TwoPointVertex S)} (hB : B ∈ d.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent B leg ↔ twoPointVertexOfLeg leg ∈ B :=
  d.componentBlock_eq_iff_mem hB _

/-- Membership of an unflattened leg in a component part. -/
def TwoPointDiagram.unflattenedLegInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (leg : TwoPointLeg S) : Prop :=
  twoPointLegVertex leg ∈ (B : Finset (TwoPointVertex S))

/-- Flattening preserves the component-membership predicate. -/
theorem TwoPointDiagram.legInComponent_iff_unflattened {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent B leg ↔
      d.unflattenedLegInComponent B (twoPointLegEquiv S leg) := by
  rw [d.legInComponent_iff_vertex_mem B.2 leg]
  rfl

/-- A leg and its partner have incident vertices in the same full component block. -/
theorem TwoPointDiagram.componentBlock_vertexOfLeg_partner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.componentBlock (twoPointVertexOfLeg (d.pairing.partner leg)) =
      d.componentBlock (twoPointVertexOfLeg leg) := by
  exact d.componentBlock_eq_of_reachable
    (d.pairing.vertexGraph_reachable_partner twoPointVertexOfLeg leg)

/-- Component-leg membership is invariant under the pairing partner permutation. -/
theorem TwoPointDiagram.legInComponent_partner_iff {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent B leg ↔ d.legInComponent B (d.pairing.partner leg) := by
  unfold TwoPointDiagram.legInComponent
  rw [d.componentBlock_vertexOfLeg_partner]

/-- The partner permutation restricted to the legs of one full component. -/
noncomputable def TwoPointDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg} :=
  d.pairing.partnerSubtypePerm (d.legInComponent B) fun leg =>
    d.legInComponent_partner_iff B leg

/-- The restricted partner has the same underlying flattened leg as the ambient partner. -/
theorem TwoPointDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card + 1))) = d.pairing.partner leg := by
  simpa only [TwoPointDiagram.restrictedPartner] using
    d.pairing.partnerSubtypePerm_val (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff B i) leg

/-- For a vacuum part, unflattened component legs are exactly the four local legs of the extracted
interaction vertices. -/
noncomputable def TwoPointDiagram.vacuumLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : TwoPointLeg S // d.unflattenedLegInComponent B leg} ≃
      ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        exact (⟨p.1.1,
          (TwoPointDiagram.mem_interactionPart_subtype
            (B : Finset (TwoPointVertex S)) p.1).2 hleg⟩, p.2)
  invFun p :=
    let v : ↥S :=
      ⟨p.1.1, TwoPointDiagram.interactionPart_subset
        (B : Finset (TwoPointVertex S)) p.1.2⟩
    ⟨Sum.inr (v, p.2), by
      change (Sum.inr v : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S))
      exact (TwoPointDiagram.mem_interactionPart_subtype
        (B : Finset (TwoPointVertex S)) v).1 p.1.2⟩
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
noncomputable def TwoPointDiagram.vacuumBlockLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg} ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).card)) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg => d.legInComponent_iff_unflattened B leg).trans
    ((d.vacuumLegDataEquiv B hVac).trans
      (quarticLegEquiv (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S)))).symm)

/-- The perfect pairing induced on a vacuum component. -/
noncomputable def TwoPointDiagram.restrictedVacuumPairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    Pairing (2 * (TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S))).card) :=
  d.pairing.restrictAlongEquiv (d.legInComponent B)
    (fun leg => d.legInComponent_partner_iff B leg) (d.vacuumBlockLegEquiv B hVac)

/-- The restricted vacuum pairing agrees with the ambient partner under the vacuum leg
reindexing. -/
theorem TwoPointDiagram.restrictedVacuumPairing_partner_vacuumBlockLegEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    (d.restrictedVacuumPairing B hVac).partner (d.vacuumBlockLegEquiv B hVac leg) =
      d.vacuumBlockLegEquiv B hVac (d.restrictedPartner B leg) := by
  simpa only [TwoPointDiagram.restrictedVacuumPairing, TwoPointDiagram.restrictedPartner] using
    d.pairing.restrictAlongEquiv_partner (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff B i) (d.vacuumBlockLegEquiv B hVac) leg

/-- Restrict a vacuum component of a two-point diagram to an ordinary quartic diagram. -/
noncomputable def TwoPointDiagram.restrictVacuumComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    QuarticDiagram InternalLabel N
      (TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
      (B : Finset (TwoPointVertex S)) v.2⟩
  pairing := d.restrictedVacuumPairing B hVac

@[simp]
theorem TwoPointDiagram.restrictVacuumComponent_pairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    (d.restrictVacuumComponent B hVac).pairing = d.restrictedVacuumPairing B hVac :=
  rfl

end Common
end SecondQuantization
