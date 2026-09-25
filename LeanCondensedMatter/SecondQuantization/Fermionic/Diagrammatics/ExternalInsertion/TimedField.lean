import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

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
