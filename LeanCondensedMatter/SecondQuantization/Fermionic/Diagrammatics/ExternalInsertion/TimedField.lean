import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

set_option linter.style.header false

/-!
# Timed-field semantics for arbitrary external insertions

This module is the first concrete fermionic consumer of the statistics-independent
`ExternalInsertionMixedOrder` layer.  It attaches a `TimedField` to each canonical external or
quartic leg, pulls that field family to mixed-time atomic positions, and transports an
`ExternalInsertionDiagram` pairing to the same mixed coordinate system.

The external time-ordering sign and the scalar interaction weight are intentionally left to the
amplitude layer.
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

/-- Field label carried by one canonical external-insertion leg. -/
def orderedExternalInsertionLegFieldLabel {E n : ℕ}
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (q : Fin n → QuarticVertexLabel Mode) :
    OrderedExternalInsertionLeg E n → ExternalFieldLabel Mode
  | .inl e => externalLabel e
  | .inr leg => quarticLocalLegExternalFieldLabel
      (Common.quarticLocalLeg (q leg.1.1) leg.2)

/-- Imaginary time carried by one canonical external-insertion leg. -/
def orderedExternalInsertionLegTime {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    OrderedExternalInsertionLeg E n → ℝ
  | .inl e => externalTime e
  | .inr leg => σ leg.1.1

/-- Time-labelled field carried by one canonical external-insertion leg. -/
def orderedExternalInsertionLegField {E n : ℕ}
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) : TimedField Mode :=
  ⟨orderedExternalInsertionLegTime externalTime σ leg,
    orderedExternalInsertionLegFieldLabel externalLabel q leg⟩

/-- Mixed-time atomic field family obtained by reading the canonical leg represented at each mixed
position. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicFieldFamily {E n : ℕ}
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + E)) → TimedField Mode :=
  fun p => orderedExternalInsertionLegField externalLabel externalTime q σ
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p)

/-- Free Gibbs pair contraction on mixed-time atomic positions. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicPairValue
    [Fintype Mode] {E n : ℕ}
    (ε : Mode → ℝ) (β : ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (a b : Fin (2 * (2 * n + E))) : ℂ :=
  timedFieldPairContraction ε β
    (externalInsertionMixedTimeOrderedAtomicFieldFamily externalLabel externalTime q σ a)
    (externalInsertionMixedTimeOrderedAtomicFieldFamily externalLabel externalTime q σ b)

/-- Slot-indexed interaction labels of an external-insertion Wick diagram. -/
def ExternalInsertionWickDiagram.vertexLabelSequence {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n) :
    Fin n → QuarticVertexLabel Mode :=
  fun v => d.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- Cast the pairing cardinality from the `Finset.univ` representation to the explicit slot count. -/
private noncomputable def externalInsertionPairingCastEquiv (E n : ℕ) :
    Pairing (2 * (Finset.univ : Finset (Fin n)).card + E) ≃ Pairing (2 * n + E) :=
  Equiv.cast (by simp)

/-- Transport a diagram pairing from fixed flattened-leg order to mixed-time atomic order. -/
noncomputable def ExternalInsertionWickDiagram.pairingInMixedOrder {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Pairing (2 * n + E) :=
  (externalInsertionPairingCastEquiv E n d.pairing).transport
    (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm

private theorem externalInsertionPairingCastEquiv_partner {E n : ℕ}
    (pairing : Pairing (2 * (Finset.univ : Finset (Fin n)).card + E))
    (p : Fin (2 * (2 * n + E))) :
    (finCongr (by simp)) ((externalInsertionPairingCastEquiv E n pairing).partner p) =
      pairing.partner ((finCongr (by simp)) p) := by
  let h : 2 * (Finset.univ : Finset (Fin n)).card + E = 2 * n + E := by
    simp
  have hcast : externalInsertionPairingCastEquiv E n pairing =
      Equiv.cast (congrArg Pairing h) pairing := by
    unfold externalInsertionPairingCastEquiv
    congr
  have hfin : (finCongr (by simp) :
      Fin (2 * (2 * n + E)) ≃
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + E))) =
      finCongr (congrArg (fun k : ℕ => 2 * k) h.symm) := by
    congr
  rw [hcast, hfin]
  exact pairing.cast_partner h p

/-- Transporting a mixed-order partner back to the fixed flattened enumeration recovers the
original diagram partner. -/
theorem ExternalInsertionWickDiagram.mixedTimeAmbientPositionEquiv_partner {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
        ((d.pairingInMixedOrder externalTime σ).partner p) =
      d.pairing.partner
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ p) := by
  change (finCongr (by simp))
      ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm
        (((externalInsertionPairingCastEquiv E n d.pairing).transport
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm).partner p)) =
    d.pairing.partner
      ((finCongr (by simp))
        ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm p))
  rw [PairingOn.transport_partner]
  simp only [Equiv.symm_symm]
  rw [(externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm_apply_apply]
  exact externalInsertionPairingCastEquiv_partner d.pairing
    ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm p)

/-- The diagram pairing as a map on canonical external/interaction leg identities. -/
noncomputable def ExternalInsertionWickDiagram.atomicLegPartner {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (leg : OrderedExternalInsertionLeg E n) : OrderedExternalInsertionLeg E n :=
  externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
    (d.pairing.partner
      ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg))

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

variable [Fintype Mode]

/-- Fermionic pairing evaluation of one external-insertion diagram in mixed-time atomic order.
Interaction couplings and the external time-ordering sign are not included here. -/
noncomputable def ExternalInsertionWickDiagram.mixedPairingValue {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  let pairing := d.pairingInMixedOrder externalTime σ
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ)

end Fermionic
end SecondQuantization
