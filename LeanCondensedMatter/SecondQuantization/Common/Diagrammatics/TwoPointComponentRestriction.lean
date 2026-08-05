import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentRestriction

set_option linter.style.header false

/-!
# Restricting vacuum components of two-point diagrams

A vacuum component of a two-point diagram contains only quartic interaction vertices. This module
extracts its interaction-vertex set, restricts the ambient perfect pairing to the legs in that
component, reindexes those legs as an ordinary quartic leg family, and packages the result as a
`QuarticDiagram`.

Restriction to the external core and amplitude factorization are separate layers.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

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

/-- The interaction vertices lying in one component part, viewed in the ambient vertex type. -/
noncomputable def TwoPointDiagram.componentInteractionVertices {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) : Finset (Fin N) :=
  ((Finset.univ.filter fun v : ↥S =>
      (Sum.inr v : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S))).map
    ⟨Subtype.val, Subtype.val_injective⟩)

@[simp]
theorem TwoPointDiagram.mem_componentInteractionVertices {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (v : ↥S) :
    (v : Fin N) ∈ d.componentInteractionVertices B ↔
      (Sum.inr v : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S)) := by
  classical
  simp [TwoPointDiagram.componentInteractionVertices]

/-- The interaction vertices extracted from a component remain in the original interaction set. -/
theorem TwoPointDiagram.componentInteractionVertices_subset {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    d.componentInteractionVertices B ⊆ S := by
  classical
  intro x hx
  simp only [TwoPointDiagram.componentInteractionVertices, Finset.mem_map] at hx
  obtain ⟨v, _, rfl⟩ := hx
  exact v.2

/-- A flattened two-point leg lies in block `B` when its incident vertex has component block `B`. -/
def TwoPointDiagram.legInComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) (leg : Fin (2 * (2 * S.card + 1))) : Prop :=
  d.componentBlock (twoPointVertexOfLeg leg) = B

/-- For an actual component part, leg membership is equivalent to membership of its incident
vertex. -/
theorem TwoPointDiagram.legInComponent_iff_vertex_mem {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent B leg ↔ twoPointVertexOfLeg leg ∈ (B : Finset (TwoPointVertex S)) :=
  d.componentBlock_eq_iff_mem B.2 (twoPointVertexOfLeg leg)

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
  rw [d.legInComponent_iff_vertex_mem B leg]
  rfl

/-- A leg and its partner have incident vertices in the same component block. -/
theorem TwoPointDiagram.componentBlock_twoPointVertexOfLeg_partner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.componentBlock (twoPointVertexOfLeg (d.pairing.partner leg)) =
      d.componentBlock (twoPointVertexOfLeg leg) := by
  by_cases h : twoPointVertexOfLeg (d.pairing.partner leg) = twoPointVertexOfLeg leg
  · rw [h]
  · exact d.componentBlock_eq_of_reachable
      (SimpleGraph.Adj.reachable
        ⟨h, d.pairing.partner leg, rfl, by rw [d.pairing.partner_involutive]⟩)

/-- A pairing partner stays in the same component part. -/
theorem TwoPointDiagram.legInComponent_partner_iff {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent B leg ↔ d.legInComponent B (d.pairing.partner leg) := by
  unfold TwoPointDiagram.legInComponent
  rw [d.componentBlock_twoPointVertexOfLeg_partner]

/-- The ambient partner permutation restricted to the legs of one component part. -/
noncomputable def TwoPointDiagram.restrictedComponentPartner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg} :=
  d.pairing.partner.subtypePerm fun leg => (d.legInComponent_partner_iff B leg).symm

/-- The restricted partner agrees with the ambient partner after forgetting the subtype. -/
theorem TwoPointDiagram.restrictedComponentPartner_val {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    (d.restrictedComponentPartner B leg : Fin (2 * (2 * S.card + 1))) =
      d.pairing.partner leg :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ leg)

/-- The component-restricted partner is involutive. -/
theorem TwoPointDiagram.restrictedComponentPartner_involutive {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S)) :
    Function.Involutive (d.restrictedComponentPartner B) := fun leg => by
  apply Subtype.ext
  rw [d.restrictedComponentPartner_val, d.restrictedComponentPartner_val,
    d.pairing.partner_involutive]

/-- The component-restricted partner has no fixed points. -/
theorem TwoPointDiagram.restrictedComponentPartner_ne_self {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : Finset (TwoPointVertex S))
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    d.restrictedComponentPartner B leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedComponentPartner_val B, h])

/-- For a vacuum part, unflattened component legs are exactly the four local legs of the extracted
interaction vertices. -/
noncomputable def TwoPointDiagram.vacuumLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : TwoPointLeg S // d.unflattenedLegInComponent B leg} ≃
      ↥(d.componentInteractionVertices B) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        exact (⟨p.1.1, (d.mem_componentInteractionVertices B p.1).2 hleg⟩, p.2)
  invFun p :=
    let v : ↥S :=
      ⟨p.1.1, d.componentInteractionVertices_subset B p.1.2⟩
    ⟨Sum.inr (v, p.2), by
      change (Sum.inr v : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S))
      exact (d.mem_componentInteractionVertices B v).1 p.1.2⟩
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
      Fin (2 * (2 * (d.componentInteractionVertices B).card)) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg => d.legInComponent_iff_unflattened B leg).trans
    ((d.vacuumLegDataEquiv B hVac).trans
      (quarticLegEquiv (d.componentInteractionVertices B)).symm)

private theorem permCongr_involutive {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : Function.Involutive p) :
    Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem permCongr_ne_self {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (x : β) :
    e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- The perfect pairing induced on a vacuum component. -/
noncomputable def TwoPointDiagram.restrictedVacuumPairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    Pairing (2 * (d.componentInteractionVertices B).card) :=
  Pairing.ofPartner
    ((d.vacuumBlockLegEquiv B hVac).permCongr
      (d.restrictedComponentPartner B))
    ⟨permCongr_involutive _ _ (d.restrictedComponentPartner_involutive B),
      permCongr_ne_self _ _ (d.restrictedComponentPartner_ne_self B)⟩

/-- The restricted vacuum pairing agrees with the ambient partner under the vacuum leg
reindexing. -/
theorem TwoPointDiagram.restrictedVacuumPairing_partner_vacuumBlockLegEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent B leg}) :
    (d.restrictedVacuumPairing B hVac).partner (d.vacuumBlockLegEquiv B hVac leg) =
      d.vacuumBlockLegEquiv B hVac (d.restrictedComponentPartner B leg) := by
  simp [TwoPointDiagram.restrictedVacuumPairing, Pairing.ofPartner,
    Equiv.permCongr_apply]

/-- Restrict a vacuum component of a two-point diagram to an ordinary quartic diagram. -/
noncomputable def TwoPointDiagram.restrictVacuumComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    QuarticDiagram InternalLabel N (d.componentInteractionVertices B) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, d.componentInteractionVertices_subset B v.2⟩
  pairing := d.restrictedVacuumPairing B hVac

@[simp]
theorem TwoPointDiagram.restrictVacuumComponent_pairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    (d.restrictVacuumComponent B hVac).pairing = d.restrictedVacuumPairing B hVac :=
  rfl

end Common
end SecondQuantization
