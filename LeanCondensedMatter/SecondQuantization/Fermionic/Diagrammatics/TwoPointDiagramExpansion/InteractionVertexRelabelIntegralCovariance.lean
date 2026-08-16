import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelCovariance
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCanonicalLocality
import LeanCondensedMatter.Analysis.OrderedSimplex.StrictAntiCongr

set_option linter.style.header false

/-!
# Interaction-vertex relabel covariance under the ordered-simplex integral

The pointwise covariance of the previous module holds only at injective interaction-time
assignments. An ordered-simplex integral only ever evaluates its integrand at strictly decreasing
assignments, which are injective, so the restriction costs nothing once integrated.

This is the whole of the transport from the pointwise layer to the integrated one: no null-set
theory and no a.e. bookkeeping beyond the single endpoint discarded inside
`orderedSimplexIntegral_congr_of_injective`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

private theorem componentShuffleIntegrand_eq_relabelAmplitude_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ)
    (hσ : Function.Injective σ) :
    twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle) σ =
      (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ'
        ((twoPointSlotTimeEquiv (n := n)) σ) := by
  calc
    twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle) σ =
      d.dysonFixedTimeAmplitude ε β g τ τ'
        ((twoPointSlotTimeEquiv (n := n))
          (fun k => σ (shuffle.ambientPermutation k))) := by
      rw [shuffle.interactionComponentShuffleIntegrand_eq_canonical
        (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
          d.1.canonicalComponentInteractionShuffle) σ]
      symm
      exact d.dysonFixedTimeAmplitude_eq_canonicalComponentShuffleIntegrand
        ε β g τ τ'
        ((twoPointSlotTimeEquiv (n := n))
          (fun k => σ (shuffle.ambientPermutation k)))
    _ = d.dysonFixedTimeAmplitude ε β g τ τ'
        (fun v => (twoPointSlotTimeEquiv (n := n)) σ
          (d.1.componentShuffleSlotPermutation shuffle v)) := by
      rw [d.1.twoPointSlotTimeEquiv_comp_ambientPermutation shuffle σ]
    _ = (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ'
        ((twoPointSlotTimeEquiv (n := n)) σ) := by
      symm
      have hslot : Function.Injective ((twoPointSlotTimeEquiv (n := n)) σ) :=
        hσ.comp (twoPointSlotEquiv (n := n)).injective
      simpa [FixedExternalTwoPointWickDiagram.relabelForComponentShuffle] using
        d.dysonFixedTimeAmplitude_relabelInteractionVertices_of_injective
          (d.1.componentShuffleSlotPermutation shuffle).symm ε β g τ τ'
          ((twoPointSlotTimeEquiv (n := n)) σ) hslot

/-- **Integrated component-shuffle covariance.** One component-shuffle term integrates to the
ordered-simplex integral of the Dyson fixed-time amplitude of the explicitly relabeled diagram.

The pointwise identity behind this is only available away from the interaction-time diagonals; the
ordered simplex never meets them. -/
theorem FixedExternalTwoPointWickDiagram.componentShuffleIntegral_eq_relabelAmplitudeIntegral
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle) :
    intervalIntegral.orderedSimplexIntegral (Finset.univ : Finset (Fin n)).card β
        (fun σ => twoPointExternalOrderSign τ τ' *
          d.1.interactionComponentShuffleIntegrand shuffle
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle) σ) =
      intervalIntegral.orderedSimplexIntegral (Finset.univ : Finset (Fin n)).card β
        (fun σ => (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ'
          ((twoPointSlotTimeEquiv (n := n)) σ)) :=
  intervalIntegral.orderedSimplexIntegral_congr_of_injective _ β hβ _ _ fun σ hσ =>
    componentShuffleIntegrand_eq_relabelAmplitude_of_injective
      d ε β g τ τ' shuffle σ hσ

end Fermionic
end SecondQuantization
