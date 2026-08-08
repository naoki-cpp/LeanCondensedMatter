import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumRestriction

set_option linter.style.header false

/-!
# External/vacuum decomposition of two-point diagrams

A two-point diagram decomposes into the unique connected component containing both distinguished
external vertices and one arbitrary quartic diagram on the complementary interaction vertices.
This is the binary decomposition needed for normalized-correlation coefficient convolution.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- External-component legs use the left summand of the binary external/vacuum leg split. -/
theorem TwoPointDiagram.externalVacuumLegEquiv_apply_externalBlockLeg
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg}) :
    TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset leg.1 =
      Sum.inl (d.externalBlockLegEquiv leg) := by
  let legU : {u : TwoPointLeg S //
      d.unflattenedLegInComponent d.externalComponentPart u} :=
    ((twoPointLegEquiv S).subtypeEquiv fun p =>
      d.legInComponent_iff_unflattened d.externalComponentPart p) leg
  have hdata : TwoPointDiagram.externalVacuumLegDataEquiv
      d.externalInteractionPart_subset (twoPointLegEquiv S leg.1) =
      Sum.inl (d.externalLegDataEquiv legU) := by
    rcases hleg : twoPointLegEquiv S leg.1 with e | ⟨v, l⟩
    · rfl
    · have hvcomp : (Sum.inr v : TwoPointVertex S) ∈ d.externalComponent 0 := by
        exact legU.2
      have hv : v.1 ∈ d.externalInteractionPart :=
        (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) v).2 hvcomp
      simp [TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.interactionExternalVacuumEquiv,
        TwoPointDiagram.externalInteractionPart, hleg, hv, legU,
        TwoPointDiagram.externalLegDataEquiv]
  unfold TwoPointDiagram.externalVacuumLegEquiv TwoPointDiagram.externalBlockLegEquiv
  simp only [Equiv.trans_apply]
  rw [hdata]
  rfl

/-- Vacuum-remainder legs use the right summand of the binary external/vacuum leg split. -/
theorem TwoPointDiagram.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg}) :
    TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset leg.1 =
      Sum.inr (d.vacuumRemainderBlockLegEquiv leg) := by
  let legU : {u : TwoPointLeg S // d.unflattenedLegInVacuumRemainder u} :=
    ((twoPointLegEquiv S).subtypeEquiv fun p =>
      not_congr (d.legInComponent_iff_unflattened d.externalComponentPart p)) leg
  have hdata : TwoPointDiagram.externalVacuumLegDataEquiv
      d.externalInteractionPart_subset (twoPointLegEquiv S leg.1) =
      Sum.inr (d.vacuumRemainderLegDataEquiv legU) := by
    rcases hleg : twoPointLegEquiv S leg.1 with e | ⟨v, l⟩
    · exact False.elim (legU.2 (d.externalVertex_mem_externalComponentPart e))
    · have hv : v.1 ∉ d.externalInteractionPart := by
        intro hmem
        apply legU.2
        exact (TwoPointDiagram.mem_interactionPart_subtype
          (d.externalComponent 0) v).1 hmem
      simp [TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.interactionExternalVacuumEquiv,
        hleg, hv, legU, TwoPointDiagram.vacuumRemainderLegDataEquiv]
  unfold TwoPointDiagram.externalVacuumLegEquiv TwoPointDiagram.vacuumRemainderBlockLegEquiv
  simp only [Equiv.trans_apply]
  rw [hdata]
  rfl

/-- The vacuum-remainder pairing agrees with the ambient restricted partner under its leg
reindexing. -/
theorem TwoPointDiagram.restrictedVacuumRemainderPairing_partner_blockLegEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg}) :
    d.restrictedVacuumRemainderPairing.partner (d.vacuumRemainderBlockLegEquiv leg) =
      d.vacuumRemainderBlockLegEquiv (d.restrictedVacuumRemainderPartner leg) := by
  simp [TwoPointDiagram.restrictedVacuumRemainderPairing, Pairing.ofPartner,
    Equiv.permCongr_apply]

/-- A flattened leg is in the external component exactly when its binary split tag is left. -/
theorem TwoPointDiagram.legInExternalComponent_iff_split_left
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    d.legInComponent (d.externalComponent 0) leg ↔
      ∃ a, TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset leg = Sum.inl a := by
  constructor
  · intro h
    let legB : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg} := ⟨leg, h⟩
    exact ⟨d.externalBlockLegEquiv legB,
      d.externalVacuumLegEquiv_apply_externalBlockLeg legB⟩
  · rintro ⟨a, ha⟩
    by_contra hnot
    let legB : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hnot⟩
    have hr := d.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg legB
    rw [ha] at hr
    cases hr

/-- Reassembling the external restriction and the complete vacuum remainder recovers the original
two-point diagram. -/
theorem TwoPointDiagram.reassemble_restrictExternal_restrictVacuumRemainder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    TwoPointDiagram.reassembleExternalVacuum d.externalInteractionPart_subset
      ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
      d.restrictVacuumRemainder = d := by
  apply TwoPointDiagram.ext
  · rfl
  · funext v
    by_cases hv : v.1 ∈ d.externalInteractionPart
    · simp [TwoPointDiagram.reassembleExternalVacuum,
        TwoPointDiagram.interactionExternalVacuumEquiv, hv,
        TwoPointDiagram.restrictExternalComponent]
    · simp [TwoPointDiagram.reassembleExternalVacuum,
        TwoPointDiagram.interactionExternalVacuumEquiv, hv,
        TwoPointDiagram.restrictVacuumRemainder]
  · apply Pairing.ext
    apply Equiv.ext
    intro leg
    let split := TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset
    cases hsplit : split leg with
    | inl a =>
        have hins : d.legInComponent (d.externalComponent 0) leg :=
          (d.legInExternalComponent_iff_split_left leg).2 ⟨a, hsplit⟩
        let legB : {leg : Fin (2 * (2 * S.card + 1)) //
          d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hins⟩
        have halign := d.externalVacuumLegEquiv_apply_externalBlockLeg legB
        have ha : a = d.externalBlockLegEquiv legB :=
          Sum.inl.inj (hsplit.symm.trans halign)
        have hleg : split.symm (Sum.inl a) = leg := by
          rw [← hsplit]
          exact split.symm_apply_apply leg
        have hpartnerInside : d.legInComponent (d.externalComponent 0)
            (d.pairing.partner leg) :=
          (d.legInComponent_partner_iff (d.externalComponent 0) leg).mp hins
        let pB : {leg : Fin (2 * (2 * S.card + 1)) //
          d.legInComponent (d.externalComponent 0) leg} :=
          ⟨d.pairing.partner leg, hpartnerInside⟩
        have hpAlign := d.externalVacuumLegEquiv_apply_externalBlockLeg pB
        have hpInv : d.pairing.partner leg =
            split.symm (Sum.inl (d.externalBlockLegEquiv pB)) := by
          have hp := congrArg split.symm hpAlign
          simpa [split] using hp
        have hrestricted :
            d.restrictedPartner (d.externalComponent 0) legB = pB := by
          apply Subtype.ext
          exact d.restrictedPartner_val (d.externalComponent 0) legB
        calc
          (TwoPointDiagram.reassembleExternalVacuum d.externalInteractionPart_subset
              ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
              d.restrictVacuumRemainder).pairing.partner leg =
              (TwoPointDiagram.reassembleExternalVacuum d.externalInteractionPart_subset
                ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
                d.restrictVacuumRemainder).pairing.partner (split.symm (Sum.inl a)) := by
                rw [hleg]
          _ = split.symm (Sum.inl (d.restrictedExternalPairing.partner a)) := by
                exact TwoPointDiagram.reassembleExternalVacuum_partner_external
                  d.externalInteractionPart_subset
                  ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
                  d.restrictVacuumRemainder a
          _ = split.symm (Sum.inl
                (d.externalBlockLegEquiv (d.restrictedPartner (d.externalComponent 0) legB))) := by
                rw [ha, d.restrictedExternalPairing_partner_externalBlockLegEquiv]
          _ = d.pairing.partner leg := by
                rw [hrestricted]
                exact hpInv.symm
    | inr a =>
        have hout : ¬ d.legInComponent (d.externalComponent 0) leg := by
          intro hins
          obtain ⟨b, hb⟩ := (d.legInExternalComponent_iff_split_left leg).1 hins
          rw [hsplit] at hb
          cases hb
        let legB : {leg : Fin (2 * (2 * S.card + 1)) //
          ¬ d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hout⟩
        have halign := d.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg legB
        have ha : a = d.vacuumRemainderBlockLegEquiv legB :=
          Sum.inr.inj (hsplit.symm.trans halign)
        have hleg : split.symm (Sum.inr a) = leg := by
          rw [← hsplit]
          exact split.symm_apply_apply leg
        have hpartnerOut : ¬ d.legInComponent (d.externalComponent 0)
            (d.pairing.partner leg) :=
          fun hp => hout ((d.legInComponent_partner_iff (d.externalComponent 0) leg).mpr hp)
        let pB : {leg : Fin (2 * (2 * S.card + 1)) //
          ¬ d.legInComponent (d.externalComponent 0) leg} :=
          ⟨d.pairing.partner leg, hpartnerOut⟩
        have hpAlign := d.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg pB
        have hpInv : d.pairing.partner leg =
            split.symm (Sum.inr (d.vacuumRemainderBlockLegEquiv pB)) := by
          have hp := congrArg split.symm hpAlign
          simpa [split] using hp
        have hrestricted : d.restrictedVacuumRemainderPartner legB = pB := by
          apply Subtype.ext
          exact d.restrictedVacuumRemainderPartner_val legB
        calc
          (TwoPointDiagram.reassembleExternalVacuum d.externalInteractionPart_subset
              ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
              d.restrictVacuumRemainder).pairing.partner leg =
              (TwoPointDiagram.reassembleExternalVacuum d.externalInteractionPart_subset
                ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
                d.restrictVacuumRemainder).pairing.partner (split.symm (Sum.inr a)) := by
                rw [hleg]
          _ = split.symm (Sum.inr (d.restrictedVacuumRemainderPairing.partner a)) := by
                exact TwoPointDiagram.reassembleExternalVacuum_partner_vacuum
                  d.externalInteractionPart_subset
                  ⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩
                  d.restrictVacuumRemainder a
          _ = split.symm (Sum.inr
                (d.vacuumRemainderBlockLegEquiv (d.restrictedVacuumRemainderPartner legB))) := by
                rw [ha, d.restrictedVacuumRemainderPairing_partner_blockLegEquiv]
          _ = d.pairing.partner leg := by
                rw [hrestricted]
                exact hpInv.symm

/-- Binary external/vacuum decomposition data on an ambient interaction set. -/
abbrev TwoPointDiagram.ExternalVacuumDecomposition
    (ExternalLabel InternalLabel : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Σ E : {E : Finset (Fin N) // E ⊆ S},
    ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E.1 ×
      QuarticDiagram InternalLabel N (S \ E.1)

/-- Decompose a two-point diagram into its connected external core and complete vacuum remainder. -/
noncomputable def TwoPointDiagram.decomposeExternalVacuum
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    TwoPointDiagram.ExternalVacuumDecomposition ExternalLabel InternalLabel N S :=
  ⟨⟨d.externalInteractionPart, d.externalInteractionPart_subset⟩,
    ⟨⟨d.restrictExternalComponent, d.restrictExternalComponent_isExternallyConnected⟩,
      d.restrictVacuumRemainder⟩⟩

end Common
end SecondQuantization
