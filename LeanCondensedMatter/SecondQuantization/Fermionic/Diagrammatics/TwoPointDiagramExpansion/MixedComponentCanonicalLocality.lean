import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.CanonicalComponentShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentContractionTimeLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentLocalTime

set_option linter.style.header false

/-!
# Canonical component locality for the two-point Dyson integrand

The canonical component shuffle assigns each local interaction slot to the rank of the corresponding
ambient interaction vertex. Equality of its local coordinate restrictions therefore gives
`ComponentTimeEq`. The crossing- and contraction-locality theorems then make the component pairing
value local without any caller-supplied transport hypotheses, and expose the pointwise Dyson
amplitude as the canonical component-shuffle integrand.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

private def ambientToTwoPointSlotTimeCanonical {n : ℕ}
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) : Fin n → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

private def twoPointSlotToAmbientTimeCanonical {n : ℕ}
    (σ : Fin n → ℝ) : Fin (Finset.univ : Finset (Fin n)).card → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

@[simp]
private theorem ambientToTwoPointSlotTimeCanonical_twoPointSlotToAmbientTimeCanonical
    {n : ℕ} (σ : Fin n → ℝ) :
    ambientToTwoPointSlotTimeCanonical (twoPointSlotToAmbientTimeCanonical σ) = σ := by
  funext i
  simp [ambientToTwoPointSlotTimeCanonical, twoPointSlotToAmbientTimeCanonical]

/-- Equality on the local coordinates of the canonical component shuffle is exactly the
component-time equality used by mixed pair transport. -/
private theorem FixedExternalTwoPointWickDiagram.componentTimeEq_of_canonicalAssignment_eq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (B : d.1.componentPartition.parts)
    (σ υ : Fin (Finset.univ : Finset (Fin n)).card → ℝ)
    (hσυ : DependentSlotEquiv.assignment
        d.1.canonicalComponentInteractionShuffle.slotEquiv σ B =
      DependentSlotEquiv.assignment
        d.1.canonicalComponentInteractionShuffle.slotEquiv υ B) :
    d.1.ComponentTimeEq B
      (ambientToTwoPointSlotTimeCanonical σ)
      (ambientToTwoPointSlotTimeCanonical υ) := by
  have hRestricted :
      d.1.interactionComponentTimeAssignment
          d.1.canonicalComponentInteractionShuffle σ B =
        d.1.interactionComponentTimeAssignment
          d.1.canonicalComponentInteractionShuffle υ B := by
    exact hσυ
  have hVertices :
      ∀ v : ↥(SecondQuantization.Common.TwoPointDiagram.interactionPart
        (B : Finset (SecondQuantization.Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))),
        ambientToTwoPointSlotTimeCanonical σ v.1 =
          ambientToTwoPointSlotTimeCanonical υ v.1 := by
    apply (d.1.canonicalComponentTimeAssignment_univ_eq_iff
      (ambientToTwoPointSlotTimeCanonical σ)
      (ambientToTwoPointSlotTimeCanonical υ) B).mp
    simpa [ambientToTwoPointSlotTimeCanonical] using hRestricted
  intro v hv
  exact hVertices ⟨v, hv⟩

variable [LinearOrder Mode] [Fintype Mode]

/-- The mixed component pairing value is local along the canonical interaction-component shuffle. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_local_canonical
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ)
    (B : d.1.componentPartition.parts) :
    DependentSlotEquiv.Local
      d.1.canonicalComponentInteractionShuffle.slotEquiv B
      (fun σ => d.mixedComponentPairingValue ε β τ τ'
        (ambientToTwoPointSlotTimeCanonical σ) B) := by
  intro σ υ hσυ
  exact d.mixedComponentPairingValue_eq_of_componentTimeEq
    ε β τ τ'
    (ambientToTwoPointSlotTimeCanonical σ)
    (ambientToTwoPointSlotTimeCanonical υ) B
    (d.componentTimeEq_of_canonicalAssignment_eq B σ υ hσυ)

/-- The signed mixed component factor is local along the canonical interaction-component shuffle. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue_local_canonical
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) :
    DependentSlotEquiv.Local
      d.1.canonicalComponentInteractionShuffle.slotEquiv B
      (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
        (ambientToTwoPointSlotTimeCanonical σ) B) := by
  exact d.mixedComponentDysonFixedTimeValue_local_of_pairingValue_local
    ε β g τ τ' d.1.canonicalComponentInteractionShuffle B
    (d.mixedComponentPairingValue_local_canonical ε β τ τ' B)

/-- The pointwise Dyson-signed two-point amplitude is the canonical component-shuffle integrand,
with no caller-supplied crossing or contraction preservation hypotheses. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_canonicalComponentShuffleIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand
          d.1.canonicalComponentInteractionShuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle)
          (twoPointSlotToAmbientTimeCanonical σ) := by
  apply d.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand_of_pairingValue_local
    ε β g τ τ' d.1.canonicalComponentInteractionShuffle
  intro B
  exact d.mixedComponentPairingValue_local_canonical ε β τ τ' B

end Fermionic
end SecondQuantization
