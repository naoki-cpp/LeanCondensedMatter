import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.CanonicalComponentTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentContractionTimeLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentLocalTime

set_option linter.style.header false

/-!
# Canonical component locality for the two-point Dyson integrand

The canonical component shuffle assigns each local interaction slot to the rank of the corresponding
ambient interaction vertex. Common owns the coordinate conversion and the resulting
`ComponentTimeEq` bridge. The crossing- and contraction-locality theorems then make the fermionic
component pairing value local without caller-supplied transport hypotheses and expose the pointwise
Dyson amplitude as the canonical component-shuffle integrand.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The mixed component pairing value is local along the canonical interaction-component shuffle. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_local_canonical
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ)
    (B : d.1.componentPartition.parts) :
    DependentSlotEquiv.Local
      d.1.canonicalComponentInteractionShuffle.slotEquiv B
      (fun σ => d.mixedComponentPairingValue ε β τ τ'
        (ambientToTwoPointSlotTimePermutation σ) B) := by
  intro σ υ hσυ
  exact d.mixedComponentPairingValue_eq_of_componentTimeEq
    ε β τ τ'
    (ambientToTwoPointSlotTimePermutation σ)
    (ambientToTwoPointSlotTimePermutation υ) B
    (d.1.componentTimeEq_of_canonicalAssignment_eq B σ υ hσυ)

/-- The signed mixed component factor is local along the canonical interaction-component shuffle. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue_local_canonical
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) :
    DependentSlotEquiv.Local
      d.1.canonicalComponentInteractionShuffle.slotEquiv B
      (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
        (ambientToTwoPointSlotTimePermutation σ) B) := by
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
          (twoPointSlotToAmbientTimePermutation σ) := by
  apply d.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand
    ε β g τ τ' d.1.canonicalComponentInteractionShuffle
  intro B
  exact d.mixedComponentDysonFixedTimeValue_local_canonical ε β g τ τ' B

end Fermionic
end SecondQuantization
