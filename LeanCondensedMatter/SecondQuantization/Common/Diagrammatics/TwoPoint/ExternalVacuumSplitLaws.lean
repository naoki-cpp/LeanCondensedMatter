import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumRestriction

set_option linter.style.header false

/-!
# Leg laws for the binary external/vacuum split

These are the four structural identities needed by the external/vacuum decomposition inverse.  They
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
    ((twoPointLegEquiv S).subtypeEquiv fun p =>
      d.legInComponent_iff_unflattened d.externalComponentPart p) leg
  apply (Equiv.sumCongr
    (twoPointLegEquiv d.externalInteractionPart)
    (quarticLegEquiv (S \ d.externalInteractionPart))).injective
  simp only [TwoPointDiagram.externalVacuumLegEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, Equiv.apply_symm_apply]
  rw [d.twoPointLegEquiv_externalBlockLegEquiv leg]
  rcases hraw : twoPointLegEquiv S leg.1 with e | ⟨v, l⟩
  · simp [TwoPointDiagram.externalVacuumLegDataEquiv,
      TwoPointDiagram.externalLegDataEquiv, legU, hraw]
  · have hvcomp : (Sum.inr v : TwoPointVertex S) ∈ d.externalComponent 0 := by
      have hmem := legU.2
      simpa [legU, hraw, TwoPointDiagram.unflattenedLegInComponent,
        TwoPointDiagram.externalComponentPart] using hmem
    have hv : v.1 ∈ d.externalInteractionPart :=
      (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) v).2 hvcomp
    simp [TwoPointDiagram.externalVacuumLegDataEquiv,
      TwoPointDiagram.interactionExternalVacuumEquiv,
      TwoPointDiagram.externalInteractionPart,
      TwoPointDiagram.externalLegDataEquiv, legU, hraw, hv]

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
  have hblock :
      quarticLegEquiv (S \ d.externalInteractionPart)
          (d.vacuumRemainderBlockLegEquiv leg) =
        d.vacuumRemainderLegDataEquiv legU := by
    change quarticLegEquiv (S \ d.externalInteractionPart)
        ((quarticLegEquiv (S \ d.externalInteractionPart)).symm
          (d.vacuumRemainderLegDataEquiv
            (((twoPointLegEquiv S).subtypeEquiv fun p =>
              not_congr (d.legInComponent_iff_unflattened d.externalComponentPart p)) leg))) = _
    rw [Equiv.apply_symm_apply]
  apply (Equiv.sumCongr
    (twoPointLegEquiv d.externalInteractionPart)
    (quarticLegEquiv (S \ d.externalInteractionPart))).injective
  simp only [TwoPointDiagram.externalVacuumLegEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, Equiv.apply_symm_apply]
  rw [hblock]
  rcases hraw : twoPointLegEquiv S leg.1 with e | ⟨v, l⟩
  · exfalso
    apply legU.2
    have he := d.externalVertex_mem_externalComponentPart e
    simpa [legU, hraw, TwoPointDiagram.unflattenedLegInVacuumRemainder,
      TwoPointDiagram.unflattenedLegInComponent] using he
  · have hv : v.1 ∉ d.externalInteractionPart := by
      intro hmem
      apply legU.2
      have hvcomp : (Sum.inr v : TwoPointVertex S) ∈ d.externalComponent 0 :=
        (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) v).1 hmem
      simpa [legU, hraw, TwoPointDiagram.unflattenedLegInVacuumRemainder,
        TwoPointDiagram.unflattenedLegInComponent,
        TwoPointDiagram.externalComponentPart] using hvcomp
    simp [TwoPointDiagram.externalVacuumLegDataEquiv,
      TwoPointDiagram.interactionExternalVacuumEquiv,
      TwoPointDiagram.vacuumRemainderLegDataEquiv, legU, hraw, hv]

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
