import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentLocalTime
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairTimeTransport

set_option linter.style.header false

/-!
# From component pair transport to local interaction-time integrands

The local-time shuffle layer requires each component pairing value to depend only on that
component's interaction-time coordinates.  The mixed component pair-transport layer isolates the two
concrete obligations behind this statement: preservation of internal crossings and preservation of
finite Gibbs contractions.

This module packages those obligations into the locality hypothesis consumed by the ordered-simplex
factorization.  It does not yet prove crossing or contraction preservation; those remain the
component-order and Gibbs-contraction tasks for the next layer.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Convert the ambient coordinates used by the finite-set shuffle API to the explicit order-`n`
interaction-time coordinates used by the fermionic two-point expansion. -/
private def ambientToTwoPointSlotTime {n : ℕ}
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) : Fin n → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

/-- Crossing and contraction preservation under equal component-local coordinates imply locality of
that component's complete mixed pairing value. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_local_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ)
    (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (hCross : ∀ σ υ : Fin (Finset.univ : Finset (Fin n)).card → ℝ,
      DependentSlotEquiv.assignment shuffle.slotEquiv σ B =
          DependentSlotEquiv.assignment shuffle.slotEquiv υ B →
        d.MixedComponentCrossingPreserving τ τ'
          (ambientToTwoPointSlotTime σ) (ambientToTwoPointSlotTime υ) B)
    (hContraction : ∀ σ υ : Fin (Finset.univ : Finset (Fin n)).card → ℝ,
      DependentSlotEquiv.assignment shuffle.slotEquiv σ B =
          DependentSlotEquiv.assignment shuffle.slotEquiv υ B →
        d.MixedComponentContractionPreserving ε β τ τ'
          (ambientToTwoPointSlotTime σ) (ambientToTwoPointSlotTime υ) B) :
    DependentSlotEquiv.Local shuffle.slotEquiv B
      (fun σ => d.mixedComponentPairingValue ε β τ τ'
        (ambientToTwoPointSlotTime σ) B) := by
  intro σ υ hσυ
  exact d.mixedComponentPairingValue_eq_of_timeTransport ε β τ τ'
    (ambientToTwoPointSlotTime σ) (ambientToTwoPointSlotTime υ) B
    (hCross σ υ hσυ) (hContraction σ υ hσυ)

/-- Crossing and contraction preservation for every component expose the signed pointwise Dyson
amplitude as the corresponding component-shuffle integrand. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (hCross : ∀ (B : d.1.componentPartition.parts)
        (σ υ : Fin (Finset.univ : Finset (Fin n)).card → ℝ),
      DependentSlotEquiv.assignment shuffle.slotEquiv σ B =
          DependentSlotEquiv.assignment shuffle.slotEquiv υ B →
        d.MixedComponentCrossingPreserving τ τ'
          (ambientToTwoPointSlotTime σ) (ambientToTwoPointSlotTime υ) B)
    (hContraction : ∀ (B : d.1.componentPartition.parts)
        (σ υ : Fin (Finset.univ : Finset (Fin n)).card → ℝ),
      DependentSlotEquiv.assignment shuffle.slotEquiv σ B =
          DependentSlotEquiv.assignment shuffle.slotEquiv υ B →
        d.MixedComponentContractionPreserving ε β τ τ'
          (ambientToTwoPointSlotTime σ) (ambientToTwoPointSlotTime υ) B)
    (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle)
          (fun k => σ (Fin.cast (by simp) k)) := by
  apply d.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand_of_pairingValue_local
    ε β g τ τ' shuffle
  intro B
  exact d.mixedComponentPairingValue_local_of_timeTransport
    ε β τ τ' shuffle B (hCross B) (hContraction B)

end Fermionic
end SecondQuantization
