import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelCovariance
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

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **Integrated component-shuffle covariance.** One component-shuffle term integrates to the
ordered-simplex integral of the Dyson fixed-time amplitude of the explicitly relabeled diagram.

The pointwise identity behind this is only available away from the interaction-time diagonals; the
ordered simplex never meets them. -/
theorem FixedExternalTwoPointWickDiagram.orderedSimplexIntegral_externalSign_mul_componentShuffleIntegrand
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
          (Common.ambientToTwoPointSlotTimePermutation σ)) :=
  intervalIntegral.orderedSimplexIntegral_congr_of_injective _ β hβ _ _ fun σ hσ =>
    d.externalSign_mul_componentShuffleIntegrand_eq_relabelForComponentShuffle_dysonFixedTimeAmplitude_of_injective
      ε β g τ τ' shuffle σ hσ

end Fermionic
end SecondQuantization
