import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentPartition

set_option linter.style.header false

/-!
# Restriction data for components of two-point diagrams

This module prepares restriction of a two-point diagram to its external component and vacuum
components.  It extracts the interaction vertices belonging to a full component part and restricts
the partner permutation to the legs of that component.  Reindexing those legs as either a smaller
two-point diagram or a quartic vacuum diagram is developed separately.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

open Classical in
/-- The interaction vertices contained in a full external-plus-interaction component part. -/
noncomputable def TwoPointDiagram.interactionPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) : Finset (Fin N) :=
  S.filter fun v =>
    ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : TwoPointVertex S) ∈ B

/-- Membership in the interaction part is membership of the corresponding interaction vertex in the
full component part. -/
theorem TwoPointDiagram.mem_interactionPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) (v : Fin N) :
    v ∈ d.interactionPart B ↔
      ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : TwoPointVertex S) ∈ B := by
  classical
  unfold TwoPointDiagram.interactionPart
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose, h⟩

/-- The interaction part of a full component is contained in the ambient interaction-vertex set. -/
theorem TwoPointDiagram.interactionPart_subset {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) :
    d.interactionPart B ⊆ S := by
  intro v hv
  obtain ⟨hvS, _⟩ := (d.mem_interactionPart B v).1 hv
  exact hvS

/-- A flattened leg belongs to `B` when the component block of its incident vertex is `B`. -/
def TwoPointDiagram.legInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : Fin (2 * (2 * S.card + 1))) : Prop :=
  d.componentBlock (twoPointVertexOfLeg leg) = B

/-- For an actual component-partition part, a leg belongs to the component exactly when its incident
vertex belongs to that part. -/
theorem TwoPointDiagram.legInComponent_iff_vertex_mem {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {B : Finset (TwoPointVertex S)} (hB : B ∈ d.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent B leg ↔ twoPointVertexOfLeg leg ∈ B :=
  d.componentBlock_eq_iff_mem hB _

/-- A leg and its partner have incident vertices in the same full component block. -/
theorem TwoPointDiagram.componentBlock_vertexOfLeg_partner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.componentBlock (twoPointVertexOfLeg (d.pairing.partner leg)) =
      d.componentBlock (twoPointVertexOfLeg leg) := by
  by_cases h : twoPointVertexOfLeg (d.pairing.partner leg) = twoPointVertexOfLeg leg
  · rw [h]
  · exact d.componentBlock_eq_of_reachable
      (SimpleGraph.Adj.reachable
        ⟨h, d.pairing.partner leg, rfl, by rw [d.pairing.partner_involutive]⟩)

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
  d.pairing.partner.subtypePerm fun leg => (d.legInComponent_partner_iff B leg).symm

/-- The restricted partner has the same underlying flattened leg as the ambient partner. -/
theorem TwoPointDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card + 1))) = d.pairing.partner leg :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ leg)

/-- The restricted partner remains an involution. -/
theorem TwoPointDiagram.restrictedPartner_involutive {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) :
    Function.Involutive (d.restrictedPartner B) := fun leg => by
  apply Subtype.ext
  rw [d.restrictedPartner_val, d.restrictedPartner_val, d.pairing.partner_involutive]

/-- The restricted partner has no fixed points. -/
theorem TwoPointDiagram.restrictedPartner_ne_self {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    d.restrictedPartner B leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedPartner_val B, h])

end Common
end SecondQuantization
