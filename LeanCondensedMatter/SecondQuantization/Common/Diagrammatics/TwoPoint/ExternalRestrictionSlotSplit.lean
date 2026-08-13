import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalSlotSplit
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestriction

set_option linter.style.header false

/-!
# External restriction agrees with the canonical slot split

The external component has two equivalent Common representations: `restrictExternalComponent`
restricts the ambient partner permutation to the component, while `externalVacuumSplit.1` reads the
left pairing of the canonical external/vacuum slot splitting.  This module proves that these
representations coincide.  The result lets downstream amplitude code use the canonical slot-split
fiber without rebuilding a second external restriction transport.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The external-component leg restriction is inverse to the left leg embedding of the canonical
external slot splitting. -/
theorem TwoPointDiagram.externalBlockLegEquiv_externalSlotLegSplitting_inl
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    d.externalBlockLegEquiv
        ⟨d.externalSlotLegSplitting (Sum.inl i),
          d.legInComponent_externalSlotLegSplitting_inl i⟩ = i := by
  obtain ⟨x, rfl⟩ :=
    (twoPointLegEquiv (TwoPointDiagram.interactionPart (d.externalComponent 0))).symm.surjective i
  cases x with
  | inl e =>
      simp [TwoPointDiagram.externalBlockLegEquiv,
        TwoPointDiagram.externalSlotLegSplitting, slotLegSplitting,
        TwoPointDiagram.externalLegDataEquiv, TwoPointDiagram.externalComponentPart,
        Combinatorics.subsetSumSdiffEquiv]
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp [TwoPointDiagram.externalBlockLegEquiv,
        TwoPointDiagram.externalSlotLegSplitting, slotLegSplitting,
        TwoPointDiagram.externalLegDataEquiv, TwoPointDiagram.externalComponentPart,
        Combinatorics.subsetSumSdiffEquiv]

/-- Restricting the ambient pairing to the external component gives exactly the left pairing of the
canonical external/vacuum slot split. -/
theorem TwoPointDiagram.restrictedExternalPairing_eq_splitLeft_externalSlotLegSplitting
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictedExternalPairing =
      d.pairing.splitLeft d.externalSlotLegSplitting d.isSplit_externalSlotLegSplitting := by
  apply Pairing.ext
  apply Equiv.ext
  intro i
  let leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg} :=
    ⟨d.externalSlotLegSplitting (Sum.inl i),
      by simpa [TwoPointDiagram.externalComponentPart] using
        d.legInComponent_externalSlotLegSplitting_inl i⟩
  have hres := d.restrictedExternalPairing_partner_externalBlockLegEquiv leg
  have hamb := Pairing.partner_splitLeft d.externalSlotLegSplitting
    d.isSplit_externalSlotLegSplitting i
  let j := (d.pairing.splitLeft d.externalSlotLegSplitting
    d.isSplit_externalSlotLegSplitting).partner i
  have hpartner :
      d.restrictedPartner (d.externalComponent 0) leg =
        ⟨d.externalSlotLegSplitting (Sum.inl j),
          by simpa [TwoPointDiagram.externalComponentPart] using
            d.legInComponent_externalSlotLegSplitting_inl j⟩ := by
    apply Subtype.ext
    exact hamb
  rw [d.externalBlockLegEquiv_externalSlotLegSplitting_inl i,
    hpartner, d.externalBlockLegEquiv_externalSlotLegSplitting_inl j] at hres
  simpa [j] using hres

/-- The restriction-based external component is the left half of the canonical external/vacuum
split. -/
theorem TwoPointDiagram.restrictExternalComponent_eq_externalVacuumSplit_fst
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictExternalComponent = d.externalVacuumSplit.1 := by
  apply TwoPointDiagram.ext
  · rfl
  · rfl
  · exact d.restrictedExternalPairing_eq_splitLeft_externalSlotLegSplitting

end Common
end SecondQuantization
