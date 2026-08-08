import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumRestriction

set_option linter.style.header false

/-!
# Leg laws for the binary external/vacuum split

These are the four structural identities needed by the external/vacuum decomposition inverse. They
keep dependent subtype transport out of the final decomposition theorem.
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
    ⟨twoPointLegEquiv S leg.1,
      (d.legInComponent_iff_unflattened d.externalComponentPart leg.1).1 leg.2⟩
  have hblock :
      twoPointLegEquiv d.externalInteractionPart (d.externalBlockLegEquiv leg) =
        d.externalLegDataEquiv legU := by
    exact d.twoPointLegEquiv_externalBlockLegEquiv leg
  have hdata :
      TwoPointDiagram.externalVacuumLegDataEquiv d.externalInteractionPart_subset
          (twoPointLegEquiv S leg.1) =
        Sum.inl (d.externalLegDataEquiv legU) := by
    rcases hraw : twoPointLegEquiv S leg.1 with e | ⟨v, l⟩
    · have hU : legU =
          ⟨Sum.inl e, d.externalVertex_mem_externalComponentPart e⟩ := by
        apply Subtype.ext
        exact hraw
      rw [hU]
      rfl
    · have hvcomp : (Sum.inr v : TwoPointVertex S) ∈ d.externalComponent 0 := by
        have hmem := legU.2
        change twoPointLegVertex (twoPointLegEquiv S leg.1) ∈
          (d.externalComponentPart : Finset (TwoPointVertex S)) at hmem
        rw [hraw] at hmem
        exact hmem
      have hlocal : d.unflattenedLegInComponent d.externalComponentPart
          (Sum.inr (v, l) : TwoPointLeg S) := by
        exact hvcomp
      have hU : legU = ⟨Sum.inr (v, l), hlocal⟩ := by
        apply Subtype.ext
        exact hraw
      rw [hU]
      simp [TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.interactionExternalVacuumEquiv,
        TwoPointDiagram.externalLegDataEquiv, hvcomp]
  have h := congrArg
    (Equiv.sumCongr (twoPointLegEquiv d.externalInteractionPart).symm
      (quarticLegEquiv (S \ d.externalInteractionPart)).symm) hdata
  rw [← hblock] at h
  simpa [TwoPointDiagram.externalVacuumLegEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, Equiv.apply_symm_apply] using h

/-- Vacuum-remainder legs use the right summand of the binary external/vacuum leg split. -/
theorem TwoPointDiagram.externalVacuumLegEquiv_apply_vacuumRemainderBlockLeg
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      ¬ d.legInComponent (d.externalComponent 0) leg}) :
    TwoPointDiagram.externalVacuumLegEquiv d.externalInteractionPart_subset leg.1 =
      Sum.inr (d.vacuumRemainderBlockLegEquiv leg) := by
  let legU : {u : TwoPointLeg S // d.unflattenedLegInVacuumRemainder u} :=
    ⟨twoPointLegEquiv S leg.1,
      (not_congr (d.legInComponent_iff_unflattened d.externalComponentPart leg.1)).1 leg.2⟩
  have hblock :
      quarticLegEquiv (S \ d.externalInteractionPart)
          (d.vacuumRemainderBlockLegEquiv leg) =
        d.vacuumRemainderLegDataEquiv legU := by
    change quarticLegEquiv (S \ d.externalInteractionPart)
        ((quarticLegEquiv (S \ d.externalInteractionPart)).symm
          (d.vacuumRemainderLegDataEquiv
            ⟨twoPointLegEquiv S leg.1,
              (not_congr (d.legInComponent_iff_unflattened
                d.externalComponentPart leg.1)).1 leg.2⟩)) = _
    rw [Equiv.apply_symm_apply]
  have hdata :
      TwoPointDiagram.externalVacuumLegDataEquiv d.externalInteractionPart_subset
          (twoPointLegEquiv S leg.1) =
        Sum.inr (d.vacuumRemainderLegDataEquiv legU) := by
    rcases hraw : twoPointLegEquiv S leg.1 with e | ⟨v, l⟩
    · have hnot := legU.2
      change ¬ d.unflattenedLegInComponent d.externalComponentPart
        (twoPointLegEquiv S leg.1) at hnot
      rw [hraw] at hnot
      exact False.elim (hnot (d.externalVertex_mem_externalComponentPart e))
    · have hnot : ¬ d.unflattenedLegInComponent d.externalComponentPart
          (Sum.inr (v, l) : TwoPointLeg S) := by
        have h := legU.2
        change ¬ d.unflattenedLegInComponent d.externalComponentPart
          (twoPointLegEquiv S leg.1) at h
        rwa [hraw] at h
      have hvnotcomp : (Sum.inr v : TwoPointVertex S) ∉ d.externalComponent 0 := by
        exact hnot
      have hnotR : d.unflattenedLegInVacuumRemainder
          (Sum.inr (v, l) : TwoPointLeg S) := by
        exact hnot
      let iU : {u : TwoPointLeg S // d.unflattenedLegInVacuumRemainder u} :=
        ⟨Sum.inr (v, l), hnotR⟩
      have hU : legU = iU := by
        apply Subtype.ext
        exact hraw
      rw [hU]
      simp [iU, TwoPointDiagram.externalVacuumLegDataEquiv,
        TwoPointDiagram.interactionExternalVacuumEquiv,
        TwoPointDiagram.vacuumRemainderLegDataEquiv, hvnotcomp]
  have h := congrArg
    (Equiv.sumCongr (twoPointLegEquiv d.externalInteractionPart).symm
      (quarticLegEquiv (S \ d.externalInteractionPart)).symm) hdata
  rw [← hblock] at h
  simpa [TwoPointDiagram.externalVacuumLegEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, Equiv.apply_symm_apply] using h

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

end Common
end SecondQuantization
