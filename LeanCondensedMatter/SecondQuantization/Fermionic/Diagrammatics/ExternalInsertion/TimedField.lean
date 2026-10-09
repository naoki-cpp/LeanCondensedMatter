import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.MixedOrderData
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Timed-field semantics for arbitrary external insertions

This module is the first concrete fermionic consumer of the statistics-independent
`ExternalInsertionMixedOrder` layer.  It attaches a `TimedField` to each canonical external or
quartic leg, pulls that field family to mixed-time atomic positions, and evaluates the finite-mode
free-Gibbs pair contraction there. Generic pairing transport and its partner coherence are owned by
the Common mixed-order pairing module.

The external time-ordering sign and the scalar interaction weight are intentionally left to the
amplitude layer.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode]

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


/-- Relabeling external and interaction slots preserves the concrete time-labelled field
on each canonical atomic leg. The maps need not be order preserving: this identity
concerns the identity of the field, not the fermionic permutation sign. -/
omit [LinearOrder Mode] in
theorem orderedExternalInsertionLegField_map
    {E₁ E₂ m n : ℕ}
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (externalLabel : Fin (2 * E₂) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E₂) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E₁ m) :
    orderedExternalInsertionLegField
        (externalLabel ∘ fExternal) (externalTime ∘ fExternal)
        (q ∘ fInteraction) (σ ∘ fInteraction) leg =
      orderedExternalInsertionLegField externalLabel externalTime q σ
        (orderedExternalInsertionLegMap fExternal fInteraction leg) := by
  cases leg with
  | inl e => rfl
  | inr p =>
      rcases p with ⟨v, l⟩
      rfl

/-- The actual finite-mode free-Gibbs contraction is invariant under the induced
relabeling of atomic legs, with both times and field labels pulled back along the
same slot maps. The endpoints retain the order `a, b`; reversing an *ambient
normalized pair* is a separate issue when transporting fermionic signs. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_map
    [Fintype Mode] {E₁ E₂ m n : ℕ}
    (ε : Mode → ℝ) (β : ℝ)
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (externalLabel : Fin (2 * E₂) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E₂) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (a b : OrderedExternalInsertionLeg E₁ m) :
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
        externalLabel externalTime q σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap fExternal fInteraction a))
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap fExternal fInteraction b)) =
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
        (externalLabel ∘ fExternal) (externalTime ∘ fExternal)
        (q ∘ fInteraction) (σ ∘ fInteraction)
        (externalInsertionMixedTimeOrderedAtomicLegPosition
          (externalTime ∘ fExternal) (σ ∘ fInteraction) a)
        (externalInsertionMixedTimeOrderedAtomicLegPosition
          (externalTime ∘ fExternal) (σ ∘ fInteraction) b) := by
  have hfield (leg : OrderedExternalInsertionLeg E₁ m) :
      externalInsertionMixedTimeOrderedAtomicFieldFamily externalLabel externalTime q σ
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
            (orderedExternalInsertionLegMap fExternal fInteraction leg)) =
        externalInsertionMixedTimeOrderedAtomicFieldFamily
          (externalLabel ∘ fExternal) (externalTime ∘ fExternal)
          (q ∘ fInteraction) (σ ∘ fInteraction)
          (externalInsertionMixedTimeOrderedAtomicLegPosition
            (externalTime ∘ fExternal) (σ ∘ fInteraction) leg) := by
    simp only [externalInsertionMixedTimeOrderedAtomicFieldFamily,
      externalInsertionMixedTimeOrderedAtomicLegEquiv_position]
    exact (orderedExternalInsertionLegField_map
      fExternal fInteraction externalLabel externalTime q σ leg).symm
  exact congrArg₂ (timedFieldPairContraction ε β) (hfield a) (hfield b)

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
