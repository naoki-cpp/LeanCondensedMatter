import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestrictionConnected

set_option linter.style.header false

/-!
# Restricting the full vacuum remainder of a two-point diagram

After removing the unique external component, all remaining interaction vertices and pairing legs
form one ordinary quartic diagram.  It may be disconnected; that is intentional, since the existing
quartic linked-cluster theorem owns the connected decomposition of this vacuum remainder.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Interaction vertices in the external component. -/
noncomputable def TwoPointDiagram.externalInteractionPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Finset (Fin N) :=
  TwoPointDiagram.interactionPart (d.externalComponent 0)

@[simp]
theorem TwoPointDiagram.externalInteractionPart_subset {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.externalInteractionPart ⊆ S :=
  TwoPointDiagram.interactionPart_subset (d.externalComponent 0)

/-- An unflattened leg lies outside the unique external component. -/
def TwoPointDiagram.unflattenedLegInVacuumRemainder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (leg : TwoPointLeg S) : Prop :=
  ¬ d.unflattenedLegInComponent d.externalComponentPart leg

/-- Legs outside the external component are exactly quartic local legs on the complement of the
external interaction set. -/
noncomputable def TwoPointDiagram.vacuumRemainderLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {leg : TwoPointLeg S // d.unflattenedLegInVacuumRemainder leg} ≃
      ↥(S \ d.externalInteractionPart) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        exact False.elim (hleg (d.externalVertex_mem_externalComponentPart e))
    | inr p =>
        have hnot : p.1.1 ∉ d.externalInteractionPart := by
          intro hmem
          apply hleg
          exact (TwoPointDiagram.mem_interactionPart_subtype
            (d.externalComponent 0) p.1).1 hmem
        exact (⟨p.1.1, Finset.mem_sdiff.mpr ⟨p.1.2, hnot⟩⟩, p.2)
  invFun p :=
    let vS : ↥S := ⟨p.1.1, (Finset.mem_sdiff.mp p.1.2).1⟩
    ⟨Sum.inr (vS, p.2), by
      intro hmem
      have hpart : (vS : Fin N) ∈ d.externalInteractionPart :=
        (TwoPointDiagram.mem_interactionPart_subtype
          (d.externalComponent 0) vS).2 hmem
      exact (Finset.mem_sdiff.mp p.1.2).2 hpart⟩
  left_inv leg := by
    rcases leg with ⟨(e | ⟨v, l⟩), hleg⟩
    · exact False.elim (hleg (d.externalVertex_mem_externalComponentPart e))
    · apply Subtype.ext
      rfl
  right_inv p := by
    rcases p with ⟨v, l⟩
    apply Prod.ext
    · exact Subtype.ext (by rfl)
    · rfl

/-- Reindex all flattened legs outside the external component as quartic legs of the vacuum
remainder. -/
noncomputable def TwoPointDiagram.vacuumRemainderBlockLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg} ≃
      Fin (2 * (2 * (S \ d.externalInteractionPart).card)) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg => by
      rw [d.legInComponent_iff_unflattened d.externalComponentPart leg]
      rfl).trans
    (d.vacuumRemainderLegDataEquiv.trans
      (quarticLegEquiv (S \ d.externalInteractionPart)).symm)

/-- The ambient partner restricted to all legs outside the external component. -/
noncomputable def TwoPointDiagram.restrictedVacuumRemainderPartner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg} :=
  d.pairing.partner.subtypePerm fun leg =>
    not_congr (d.legInComponent_partner_iff (d.externalComponent 0) leg).symm

@[simp]
theorem TwoPointDiagram.restrictedVacuumRemainderPartner_val {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg}) :
    (d.restrictedVacuumRemainderPartner leg : Fin (2 * (2 * S.card + 1))) =
      d.pairing.partner leg :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ leg)

private theorem restrictedVacuumRemainderPartner_involutive {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Function.Involutive d.restrictedVacuumRemainderPartner := fun leg => by
  apply Subtype.ext
  rw [d.restrictedVacuumRemainderPartner_val,
    d.restrictedVacuumRemainderPartner_val, d.pairing.partner_involutive]

private theorem restrictedVacuumRemainderPartner_ne_self {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg}) :
    d.restrictedVacuumRemainderPartner leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedVacuumRemainderPartner_val, h])

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

/-- Perfect pairing of the complete vacuum remainder. -/
noncomputable def TwoPointDiagram.restrictedVacuumRemainderPairing {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Pairing (2 * (S \ d.externalInteractionPart).card) :=
  Pairing.ofPartner
    (d.vacuumRemainderBlockLegEquiv.permCongr d.restrictedVacuumRemainderPartner)
    ⟨permCongr_involutive _ _ d.restrictedVacuumRemainderPartner_involutive,
      permCongr_ne_self _ _ d.restrictedVacuumRemainderPartner_ne_self⟩

/-- The entire complement of the external component as one ordinary quartic diagram. -/
noncomputable def TwoPointDiagram.restrictVacuumRemainder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    QuarticDiagram InternalLabel N (S \ d.externalInteractionPart) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
  pairing := d.restrictedVacuumRemainderPairing

end Common
end SecondQuantization
