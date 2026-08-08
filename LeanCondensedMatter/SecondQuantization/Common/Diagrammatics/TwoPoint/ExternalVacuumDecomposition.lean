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
  have hunflat := (d.legInComponent_iff_unflattened d.externalComponentPart leg.1).1 leg.2
  cases hleg : twoPointLegEquiv S leg.1 with
  | inl e =>
      simp [TwoPointDiagram.externalVacuumLegEquiv,
        TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.externalBlockLegEquiv, TwoPointDiagram.externalLegDataEquiv,
        hleg]
  | inr p =>
      have hp : p.1.1 ∈ d.externalInteractionPart :=
        (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) p.1).2 (by
          simpa [hleg] using hunflat)
      simp [TwoPointDiagram.externalVacuumLegEquiv,
        TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.externalBlockLegEquiv, TwoPointDiagram.externalLegDataEquiv,
        TwoPointDiagram.interactionExternalVacuumEquiv,
        TwoPointDiagram.externalInteractionPart, hleg, hp]

/-- Vacuum-remainder legs use the right summand of the binary external/vacuum leg split. -/
theorem TwoPointDiagram.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg}) :
    TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset leg.1 =
      Sum.inr (d.vacuumRemainderBlockLegEquiv leg) := by
  have hunflat : d.unflattenedLegInVacuumRemainder (twoPointLegEquiv S leg.1) := by
    rw [← d.legInComponent_iff_unflattened d.externalComponentPart leg.1]
    exact leg.2
  cases hleg : twoPointLegEquiv S leg.1 with
  | inl e =>
      exact False.elim (hunflat (by
        simpa [hleg] using d.externalVertex_mem_externalComponentPart e))
  | inr p =>
      have hp : p.1.1 ∉ d.externalInteractionPart := by
        intro hmem
        apply hunflat
        change (Sum.inr p.1 : TwoPointVertex S) ∈ d.externalComponent 0
        exact (TwoPointDiagram.mem_interactionPart_subtype
          (d.externalComponent 0) p.1).1 hmem
      simp [TwoPointDiagram.externalVacuumLegEquiv,
        TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.vacuumRemainderBlockLegEquiv,
        TwoPointDiagram.vacuumRemainderLegDataEquiv,
        TwoPointDiagram.interactionExternalVacuumEquiv, hleg, hp]

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
    exact Sum.noConfusion hr

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
    · have hsplit : TwoPointDiagram.interactionExternalVacuumEquiv
          d.externalInteractionPart_subset v =
          Sum.inl ⟨v.1, hv⟩ := by
        simp [TwoPointDiagram.interactionExternalVacuumEquiv, hv]
      change (match TwoPointDiagram.interactionExternalVacuumEquiv
        d.externalInteractionPart_subset v with
        | Sum.inl w => d.restrictExternalComponent.vertexLabel w
        | Sum.inr w => d.restrictVacuumRemainder.vertexLabel w) = d.vertexLabel v
      rw [hsplit]
      rfl
    · have hsplit : TwoPointDiagram.interactionExternalVacuumEquiv
          d.externalInteractionPart_subset v =
          Sum.inr ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ := by
        simp [TwoPointDiagram.interactionExternalVacuumEquiv, hv]
      change (match TwoPointDiagram.interactionExternalVacuumEquiv
        d.externalInteractionPart_subset v with
        | Sum.inl w => d.restrictExternalComponent.vertexLabel w
        | Sum.inr w => d.restrictVacuumRemainder.vertexLabel w) = d.vertexLabel v
      rw [hsplit]
      rfl
  · apply Pairing.ext
    ext leg
    let split := TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset
    cases hsplit : split leg with
    | inl a =>
        have hins : d.legInComponent (d.externalComponent 0) leg :=
          (d.legInExternalComponent_iff_split_left leg).2 ⟨a, hsplit⟩
        let legB : {leg : Fin (2 * (2 * S.card + 1)) //
          d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hins⟩
        have halign := d.externalVacuumLegEquiv_apply_externalBlockLeg legB
        rw [hsplit] at halign
        have ha : a = d.externalBlockLegEquiv legB := Sum.inl.inj halign
        have hleg : leg = split.symm (Sum.inl a) := by
          rw [← hsplit]
          exact split.symm_apply_apply leg
        rw [hleg, TwoPointDiagram.reassembleExternalVacuum_partner_external]
        apply split.injective
        simp only [split, Equiv.apply_symm_apply]
        rw [ha, d.restrictedExternalPairing_partner_externalBlockLegEquiv]
        have hpartnerInside : d.legInComponent (d.externalComponent 0) (d.pairing.partner leg) :=
          (d.legInComponent_partner_iff (d.externalComponent 0) leg).mp hins
        let pB : {leg : Fin (2 * (2 * S.card + 1)) //
          d.legInComponent (d.externalComponent 0) leg} :=
          ⟨d.pairing.partner leg, hpartnerInside⟩
        have hpAlign := d.externalVacuumLegEquiv_apply_externalBlockLeg pB
        simpa [legB, pB, TwoPointDiagram.restrictedPartner_val] using hpAlign.symm
    | inr a =>
        have hout : ¬ d.legInComponent (d.externalComponent 0) leg := by
          intro hins
          obtain ⟨b, hb⟩ := (d.legInExternalComponent_iff_split_left leg).1 hins
          rw [hsplit] at hb
          exact Sum.noConfusion hb
        let legB : {leg : Fin (2 * (2 * S.card + 1)) //
          ¬ d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hout⟩
        have halign := d.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg legB
        rw [hsplit] at halign
        have ha : a = d.vacuumRemainderBlockLegEquiv legB := Sum.inr.inj halign
        have hleg : leg = split.symm (Sum.inr a) := by
          rw [← hsplit]
          exact split.symm_apply_apply leg
        rw [hleg, TwoPointDiagram.reassembleExternalVacuum_partner_vacuum]
        apply split.injective
        simp only [split, Equiv.apply_symm_apply]
        rw [ha, d.restrictedVacuumRemainderPairing_partner_blockLegEquiv]
        have hpartnerOut : ¬ d.legInComponent (d.externalComponent 0) (d.pairing.partner leg) :=
          fun hp => hout ((d.legInComponent_partner_iff (d.externalComponent 0) leg).mpr hp)
        let pB : {leg : Fin (2 * (2 * S.card + 1)) //
          ¬ d.legInComponent (d.externalComponent 0) leg} :=
          ⟨d.pairing.partner leg, hpartnerOut⟩
        have hpAlign := d.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg pB
        simpa [legB, pB, TwoPointDiagram.restrictedVacuumRemainderPartner_val] using hpAlign.symm

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
