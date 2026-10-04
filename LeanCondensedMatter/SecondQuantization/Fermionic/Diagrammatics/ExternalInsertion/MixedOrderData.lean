import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false

/-!
# Kernel-free mixed-order data for fermionic external insertions

This module names the concrete fermionic external-insertion diagram and transports its pairing
through the statistics-independent mixed-time position equivalence. It contains no timed field or
thermal kernel definitions.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- Fermionic external-insertion diagrams with ordered interaction slots. -/
abbrev ExternalInsertionWickDiagram (Mode : Type*) (E n : ℕ) : Type _ :=
  Common.ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
    E n (Finset.univ : Finset (Fin n))

/-- Slot-indexed interaction labels of an external-insertion Wick diagram. -/
def ExternalInsertionWickDiagram.vertexLabelSequence {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n) :
    Fin n → QuarticVertexLabel Mode :=
  fun v => d.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- The diagram pairing as a map on canonical external/interaction leg identities. -/
noncomputable def ExternalInsertionWickDiagram.atomicLegPartner {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (leg : OrderedExternalInsertionLeg E n) : OrderedExternalInsertionLeg E n :=
  externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
    (d.pairing.partner
      ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg))

omit [LinearOrder Mode] in
/-- The mixed-order partner of the position selected by a canonical leg is the mixed position of
that leg's diagram partner. -/
theorem ExternalInsertionWickDiagram.pairingInMixedOrder_partner_legPosition {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    (d.pairingInMixedOrder externalTime σ).partner
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) =
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (d.atomicLegPartner leg) := by
  have hpos :
      externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg := by
    apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).injective
    rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
      externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
      Equiv.apply_symm_apply]
  apply (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).injective
  rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    ← externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    d.mixedTimeAmbientPositionEquiv_partner,
    hpos,
    ExternalInsertionWickDiagram.atomicLegPartner]


end Fermionic
end SecondQuantization
