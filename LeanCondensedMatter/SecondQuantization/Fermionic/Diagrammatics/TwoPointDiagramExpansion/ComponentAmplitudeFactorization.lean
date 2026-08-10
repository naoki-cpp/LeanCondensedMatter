import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelIntegralCovariance
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentShuffleIntegrability
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonIntegral

set_option linter.style.header false

/-!
# The component-shuffle orbit of a diagram integrates to a product over its components

Summing the integrated Dyson amplitude over the component-shuffle relabelings of one fixed-external
two-point diagram gives the product of the component-local integrated factors, times the external
ordering sign.

Nothing new is proved here. The three inputs are already available:

* each shuffle term is the amplitude of an explicitly relabeled diagram under the ordered-simplex
  integral, by strict-order relabel covariance;
* the sum over shuffles of the localized integrands is the product over components of their
  ordered-simplex integrals, by the finite-family shuffle theorem;
* the coordinate count `n` and its `Finset.card` presentation differ only by `Fin.cast`.

In particular no per-diagram stabilizer or orbit cardinality enters: the shuffle type is summed over
directly, and each of its elements names a diagram through `relabelForComponentShuffle`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **Shuffle-orbit amplitude sum.** The integrated Dyson amplitudes of the component-shuffle
relabelings of a diagram sum to the external ordering sign times the product of the component-local
integrated factors. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentInteractionShuffle_dysonAmplitude_relabelForComponentShuffle_eq_prod
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          intervalIntegral.orderedSimplexIntegral (d.1.interactionComponentSize B) β
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle B) := by
  have hcard : n = (Finset.univ : Finset (Fin n)).card := by simp
  have hterm (shuffle : d.1.ComponentInteractionShuffle) :
      (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ' =
        twoPointExternalOrderSign τ τ' *
          intervalIntegral.orderedSimplexIntegral (Finset.univ : Finset (Fin n)).card β
            (d.1.interactionComponentShuffleIntegrand shuffle
              (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
                d.1.canonicalComponentInteractionShuffle)) := by
    have hcast :
        intervalIntegral.orderedSimplexIntegral n β
            (fun σ =>
              (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ' σ) =
          intervalIntegral.orderedSimplexIntegral (Finset.univ : Finset (Fin n)).card β
            (fun σ =>
              (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ'
                (ambientToTwoPointSlotTimePermutation σ)) :=
      intervalIntegral.orderedSimplexIntegral_cast hcard β _
    rw [(d.relabelForComponentShuffle
        shuffle).dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g τ τ',
      hcast,
      ← d.orderedSimplexIntegral_externalSign_mul_componentShuffleIntegrand ε β hβ g τ τ' shuffle,
      intervalIntegral.orderedSimplexIntegral_smul]
  rw [Finset.sum_congr rfl fun shuffle _ => hterm shuffle, ← Finset.mul_sum,
    d.sum_componentInteractionShuffle_orderedSimplexIntegral_mixedComponentDysonLocalIntegrand_eq_prod
      ε β g τ τ' d.1.canonicalComponentInteractionShuffle]

end Fermionic
end SecondQuantization
