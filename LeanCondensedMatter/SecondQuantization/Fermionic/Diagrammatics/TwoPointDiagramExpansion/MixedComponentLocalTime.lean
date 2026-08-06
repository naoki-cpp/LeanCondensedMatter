import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentLocalTime
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Local interaction-time interface for two-point Dyson component factors

The Common component-shuffle API can split an ordered-simplex integral once every signed component
factor has been identified with a function of that component's local interaction times. This module
packages that identification for the fermionic two-point expansion.

The complete locality statement is reduced to the mixed component pairing value: the Dyson sign and
quartic coupling product are independent of the interaction-time assignment. The remaining work is
therefore the order-theoretic locality of the component crossing weight and pair-contraction product.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Convert the ambient time coordinates used by the finite-set Common API to the explicit order-`n`
slot coordinates used by the fermionic two-point expansion. -/
private def ambientToTwoPointSlotTime {n : ℕ}
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) : Fin n → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

/-- Convert explicit order-`n` slot coordinates to the ambient finite-set coordinates. -/
private def twoPointSlotToAmbientTime {n : ℕ}
    (σ : Fin n → ℝ) : Fin (Finset.univ : Finset (Fin n)).card → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

@[simp]
private theorem ambientToTwoPointSlotTime_twoPointSlotToAmbientTime
    {n : ℕ} (σ : Fin n → ℝ) :
    ambientToTwoPointSlotTime (twoPointSlotToAmbientTime σ) = σ := by
  funext i
  simp [ambientToTwoPointSlotTime, twoPointSlotToAmbientTime]

@[simp]
private theorem twoPointSlotToAmbientTime_ambientToTwoPointSlotTime
    {n : ℕ} (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    twoPointSlotToAmbientTime (ambientToTwoPointSlotTime σ) = σ := by
  funext i
  simp [ambientToTwoPointSlotTime, twoPointSlotToAmbientTime]

/-- Local interaction-time integrand obtained from one ambient signed component factor along a
chosen component interaction shuffle. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    (Fin (d.1.interactionComponentSize B) → ℝ) → ℂ :=
  d.1.localizeInteractionComponentIntegrand shuffle B
    (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
      (ambientToTwoPointSlotTime σ) B)

/-- Locality of the mixed component pairing value implies locality of the complete Dyson-signed
component factor, because its Dyson sign and coupling weight do not depend on interaction times. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue_local_of_pairingValue_local
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (hPairing : d.1.InteractionComponentLocal shuffle B
      (fun σ => d.mixedComponentPairingValue ε β τ τ'
        (ambientToTwoPointSlotTime σ) B)) :
    d.1.InteractionComponentLocal shuffle B
      (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
        (ambientToTwoPointSlotTime σ) B) := by
  intro σ υ hσυ
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  change d.mixedComponentDysonSign B *
      (d.mixedComponentVertexWeight g B *
        d.mixedComponentPairingValue ε β τ τ'
          (ambientToTwoPointSlotTime σ) B) =
    d.mixedComponentDysonSign B *
      (d.mixedComponentVertexWeight g B *
        d.mixedComponentPairingValue ε β τ τ'
          (ambientToTwoPointSlotTime υ) B)
  rw [hPairing σ υ hσυ]

/-- Once every signed component factor is local along `shuffle`, the pointwise Dyson amplitude is the
external ordering sign times the corresponding component-shuffle integrand. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (hLocal : ∀ B : d.1.componentPartition.parts,
      d.1.InteractionComponentLocal shuffle B
        (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
          (ambientToTwoPointSlotTime σ) B))
    (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle)
          (twoPointSlotToAmbientTime σ) := by
  rw [d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components]
  apply congrArg (fun z : ℂ => twoPointExternalOrderSign τ τ' * z)
  let F : ∀ B : d.1.componentPartition.parts,
      (Fin (Finset.univ : Finset (Fin n)).card → ℝ) → ℂ :=
    fun B υ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
      (ambientToTwoPointSlotTime υ) B
  calc
    (∏ B : d.1.componentPartition.parts,
        d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) =
      ∏ B : d.1.componentPartition.parts,
        F B (twoPointSlotToAmbientTime σ) := by
      apply Fintype.prod_congr
      intro B
      simp [F]
    _ = d.1.interactionComponentShuffleIntegrand shuffle
        (fun B => d.1.localizeInteractionComponentIntegrand shuffle B (F B))
        (twoPointSlotToAmbientTime σ) :=
      d.1.prod_eq_interactionComponentShuffleIntegrand_localize shuffle F hLocal
        (twoPointSlotToAmbientTime σ)
    _ = d.1.interactionComponentShuffleIntegrand shuffle
        (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle)
        (twoPointSlotToAmbientTime σ) := by
      rfl

/-- Pairing-value locality is the only fermionic hypothesis needed to expose the pointwise Dyson
amplitude as a component-shuffle integrand. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand_of_pairingValue_local
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (hPairing : ∀ B : d.1.componentPartition.parts,
      d.1.InteractionComponentLocal shuffle B
        (fun σ => d.mixedComponentPairingValue ε β τ τ'
          (ambientToTwoPointSlotTime σ) B))
    (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle)
          (twoPointSlotToAmbientTime σ) := by
  apply d.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand
    ε β g τ τ' shuffle
  intro B
  exact d.mixedComponentDysonFixedTimeValue_local_of_pairingValue_local
    ε β g τ τ' shuffle B (hPairing B)

/-- The localized signed component integrands satisfy the finite-family ordered-simplex shuffle
product identity. This is the analytic exit point once their continuity has been proved. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentInteractionShuffle_orderedSimplexIntegral_mixedComponentDysonLocalIntegrand_eq_prod
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (baseShuffle : d.1.ComponentInteractionShuffle)
    (hContinuous : ∀ B : d.1.componentPartition.parts,
      Continuous (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle B)) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
      intervalIntegral.orderedSimplexIntegral
        (Finset.univ : Finset (Fin n)).card β
        (d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle))) =
      ∏ B : d.1.componentPartition.parts,
        intervalIntegral.orderedSimplexIntegral
          (d.1.interactionComponentSize B) β
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle B) := by
  exact d.1.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_prod β
    (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle) hContinuous

end Fermionic
end SecondQuantization
