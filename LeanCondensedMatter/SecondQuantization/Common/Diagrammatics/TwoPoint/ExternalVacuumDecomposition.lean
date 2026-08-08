import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumSplitLaws

set_option linter.style.header false

/-!
# External/vacuum decomposition of two-point diagrams

A two-point diagram decomposes into the unique connected component containing both distinguished
external vertices and one arbitrary quartic diagram on the complementary interaction vertices.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

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
    funext leg
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
          change pB.1 = split.symm (Sum.inl (d.externalBlockLegEquiv pB))
          simpa [split] using congrArg split.symm hpAlign
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
          change pB.1 = split.symm (Sum.inr (d.vacuumRemainderBlockLegEquiv pB))
          simpa [split] using congrArg split.symm hpAlign
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
