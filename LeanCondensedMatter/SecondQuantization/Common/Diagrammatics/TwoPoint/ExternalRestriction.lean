import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalConnectivity

set_option linter.style.header false

/-!
# Restricting the external component of a two-point diagram

The two distinguished external vertices are necessarily connected: a component containing only one
external leg would have odd cardinality and could not carry the restricted perfect pairing. Their
common component therefore contains both one-legged external vertices together with a subset of the
quartic interaction vertices. This module reindexes its legs, transports the restricted partner
permutation to a new perfect pairing, and packages the result as a smaller `TwoPointDiagram`.

Reassembly and amplitude factorization are developed separately.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Every external vertex lies in the common external component. -/
theorem TwoPointDiagram.externalVertex_mem_externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    (Sum.inl e : TwoPointVertex S) ∈
      (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  fin_cases e
  · simpa [TwoPointDiagram.externalComponentPart, TwoPointDiagram.externalComponent] using
      d.self_mem_componentBlock (Sum.inl (0 : Fin 2) : TwoPointVertex S)
  · rw [show (d.externalComponentPart : Finset (TwoPointVertex S)) =
      d.externalComponent 0 by rfl, d.externalComponent_zero_eq_one]
    simpa [TwoPointDiagram.externalComponent] using
      d.self_mem_componentBlock (Sum.inl (1 : Fin 2) : TwoPointVertex S)

/-- The unflattened legs in the common external component are exactly two external legs and the four
local legs of each interaction vertex in that component. -/
noncomputable def TwoPointDiagram.externalLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {leg : TwoPointLeg S // d.unflattenedLegInComponent d.externalComponentPart leg} ≃
      TwoPointLeg (TwoPointDiagram.interactionPart (d.externalComponent 0)) where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact Sum.inl e
    | inr p =>
        exact Sum.inr
          (⟨p.1.1, (TwoPointDiagram.mem_interactionPart_subtype
            (d.externalComponent 0) p.1).2 hleg⟩, p.2)
  invFun leg := by
    cases leg with
    | inl e =>
        exact ⟨Sum.inl e, d.externalVertex_mem_externalComponentPart e⟩
    | inr p =>
        let v : ↥S :=
          ⟨p.1.1, TwoPointDiagram.interactionPart_subset
            (d.externalComponent 0) p.1.2⟩
        exact ⟨Sum.inr (v, p.2), by
          change (Sum.inr v : TwoPointVertex S) ∈ d.externalComponent 0
          exact (TwoPointDiagram.mem_interactionPart_subtype
            (d.externalComponent 0) v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        apply Subtype.ext
        rfl
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv leg := by
    cases leg with
    | inl e => rfl
    | inr p =>
        rcases p with ⟨v, l⟩
        apply congrArg Sum.inr
        apply Prod.ext
        · exact Subtype.ext (by rfl)
        · rfl

/-- Reindex the flattened legs of the common external component as the flattened legs of a smaller
two-point diagram. -/
noncomputable def TwoPointDiagram.externalBlockLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent (d.externalComponent 0) leg} ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (d.externalComponent 0)).card + 1)) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened d.externalComponentPart leg).trans
    ((d.externalLegDataEquiv).trans
      (twoPointLegEquiv (TwoPointDiagram.interactionPart (d.externalComponent 0))).symm)

private theorem external_permCongr_involutive {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : Function.Involutive p) :
    Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem external_permCongr_ne_self {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (x : β) :
    e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- The perfect pairing induced on the common external component. -/
noncomputable def TwoPointDiagram.restrictedExternalPairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Pairing (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1) :=
  Pairing.ofPartner
    ((d.externalBlockLegEquiv).permCongr
      (d.restrictedPartner (d.externalComponent 0)))
    ⟨external_permCongr_involutive _ _
        (d.restrictedPartner_involutive (d.externalComponent 0)),
      external_permCongr_ne_self _ _
        (d.restrictedPartner_ne_self (d.externalComponent 0))⟩

/-- The restricted external pairing agrees with the ambient partner under the external-component leg
reindexing. -/
theorem TwoPointDiagram.restrictedExternalPairing_partner_externalBlockLegEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg}) :
    d.restrictedExternalPairing.partner (d.externalBlockLegEquiv leg) =
      d.externalBlockLegEquiv
        (d.restrictedPartner (d.externalComponent 0) leg) := by
  simp [TwoPointDiagram.restrictedExternalPairing, Pairing.ofPartner,
    Equiv.permCongr_apply]

/-- Restrict the common external component to a smaller two-point diagram. -/
noncomputable def TwoPointDiagram.restrictExternalComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    TwoPointDiagram ExternalLabel InternalLabel N
      (TwoPointDiagram.interactionPart (d.externalComponent 0)) where
  externalLabel := d.externalLabel
  vertexLabel v :=
    d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
      (d.externalComponent 0) v.2⟩
  pairing := d.restrictedExternalPairing

@[simp]
theorem TwoPointDiagram.restrictExternalComponent_externalLabel {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    d.restrictExternalComponent.externalLabel e = d.externalLabel e :=
  rfl

@[simp]
theorem TwoPointDiagram.restrictExternalComponent_vertexLabel {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v : ↥(TwoPointDiagram.interactionPart (d.externalComponent 0))) :
    d.restrictExternalComponent.vertexLabel v =
      d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
        (d.externalComponent 0) v.2⟩ :=
  rfl

@[simp]
theorem TwoPointDiagram.restrictExternalComponent_pairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictExternalComponent.pairing = d.restrictedExternalPairing :=
  rfl

end Common
end SecondQuantization
