import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentRestriction

set_option linter.style.header false

/-!
# Restricting the external component of a two-point diagram

When the two distinguished external vertices are connected, their common component contains both
one-legged external vertices together with a subset of the quartic interaction vertices.  This
module reindexes the legs of that component, transports its restricted partner permutation to a
new perfect pairing, and packages the result as a smaller `TwoPointDiagram`.

Reassembly and amplitude factorization are developed separately.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The component-partition part containing external vertex `0`. -/
noncomputable def TwoPointDiagram.externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.componentPartition.parts :=
  ⟨d.externalComponent 0, d.externalComponent_mem_componentPartition 0⟩

/-- If the two external vertices are connected, every external vertex lies in their common
component. -/
theorem TwoPointDiagram.externalVertex_mem_externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) (e : Fin 2) :
    (Sum.inl e : TwoPointVertex S) ∈
      (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  fin_cases e
  · simpa [TwoPointDiagram.externalComponentPart, TwoPointDiagram.externalComponent] using
      d.self_mem_componentBlock (Sum.inl (0 : Fin 2) : TwoPointVertex S)
  · have hcomp : d.externalComponent 0 = d.externalComponent 1 :=
      (d.externalVerticesConnected_iff_externalComponent_eq).1 hExt
    rw [show (d.externalComponentPart : Finset (TwoPointVertex S)) =
      d.externalComponent 0 by rfl, hcomp]
    simpa [TwoPointDiagram.externalComponent] using
      d.self_mem_componentBlock (Sum.inl (1 : Fin 2) : TwoPointVertex S)

/-- The unflattened legs in the common external component are exactly two external legs and the four
local legs of each interaction vertex in that component. -/
noncomputable def TwoPointDiagram.externalLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) :
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
        exact ⟨Sum.inl e, d.externalVertex_mem_externalComponentPart hExt e⟩
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
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) :
    {leg : Fin (2 * (2 * S.card + 1)) // d.legInComponent (d.externalComponent 0) leg} ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (d.externalComponent 0)).card + 1)) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened d.externalComponentPart leg).trans
    ((d.externalLegDataEquiv hExt).trans
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
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) :
    Pairing (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1) :=
  Pairing.ofPartner
    ((d.externalBlockLegEquiv hExt).permCongr
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
    (hExt : d.ExternalVerticesConnected)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg}) :
    (d.restrictedExternalPairing hExt).partner (d.externalBlockLegEquiv hExt leg) =
      d.externalBlockLegEquiv hExt
        (d.restrictedPartner (d.externalComponent 0) leg) := by
  simp [TwoPointDiagram.restrictedExternalPairing, Pairing.ofPartner,
    Equiv.permCongr_apply]

/-- Restrict the common external component to a smaller two-point diagram. -/
noncomputable def TwoPointDiagram.restrictExternalComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) :
    TwoPointDiagram ExternalLabel InternalLabel N
      (TwoPointDiagram.interactionPart (d.externalComponent 0)) where
  externalLabel := d.externalLabel
  vertexLabel v :=
    d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
      (d.externalComponent 0) v.2⟩
  pairing := d.restrictedExternalPairing hExt

@[simp]
theorem TwoPointDiagram.restrictExternalComponent_externalLabel {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) (e : Fin 2) :
    (d.restrictExternalComponent hExt).externalLabel e = d.externalLabel e :=
  rfl

@[simp]
theorem TwoPointDiagram.restrictExternalComponent_pairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : d.ExternalVerticesConnected) :
    (d.restrictExternalComponent hExt).pairing = d.restrictedExternalPairing hExt :=
  rfl

end Common
end SecondQuantization
