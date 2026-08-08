import LeanCondensedMatter.Analysis.OrderedSimplex.AlmostEverywhere
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelCovariance
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentShuffleIntegrability
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonIntegral

set_option linter.style.header false

/-!
# Integrated component-shuffle factorization

The pointwise relabel covariance needed for the external-leg LCT holds away from interaction-time
collisions. `orderedSimplexIntegral_congr_of_injective` removes exactly those null diagonals, so
each shuffled component term integrates to the Dyson amplitude of the corresponding relabeled
fixed diagram. Combining this with the measurable finite-family shuffle theorem gives the
integrated component product without any exact equal-time covariance theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- One component-shuffle integral is the Dyson amplitude of the explicitly relabeled diagram,
up to the common external ordering sign. -/
theorem FixedExternalTwoPointWickDiagram.externalSign_mul_orderedSimplexIntegral_componentShuffle_eq_relabelDysonAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle) :
    twoPointExternalOrderSign τ τ' *
        intervalIntegral.orderedSimplexIntegral
          (Finset.univ : Finset (Fin n)).card β
          (d.1.interactionComponentShuffleIntegrand shuffle
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle)) =
      (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ' := by
  rw [← intervalIntegral.orderedSimplexIntegral_smul]
  rw [FixedExternalTwoPointWickDiagram.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude
    (d.relabelForComponentShuffle shuffle) ε β g τ τ']
  let hdim : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [intervalIntegral.orderedSimplexIntegral_cast hdim]
  apply intervalIntegral.orderedSimplexIntegral_congr_of_injective
  intro σ hσ
  let σambient : Fin (Finset.univ : Finset (Fin n)).card → ℝ :=
    fun i => σ (Fin.cast hdim i)
  have hσambient : Function.Injective σambient := by
    intro a b hab
    apply (finCongr hdim).injective
    exact hσ hab
  have hslot : ambientToTwoPointSlotTimePermutation σambient = σ := by
    funext i
    simp [ambientToTwoPointSlotTimePermutation, σambient, hdim]
  have hcov :=
    d.externalSign_mul_componentShuffleIntegrand_eq_relabelForComponentShuffle_dysonFixedTimeAmplitude_of_injective
      ε β g τ τ' shuffle σambient hσambient
  rw [hslot] at hcov
  exact hcov

/-- Summing the integrated relabeled amplitudes over all component shuffles gives the product of
component-local ordered-simplex integrals, with the common external ordering sign. -/
theorem FixedExternalTwoPointWickDiagram.sum_relabelForComponentShuffle_dysonAmplitude_eq_externalSign_mul_prod_componentIntegrals
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          intervalIntegral.orderedSimplexIntegral
            (d.1.interactionComponentSize B) β
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle B) := by
  calc
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      ∑ shuffle : d.1.ComponentInteractionShuffle,
        twoPointExternalOrderSign τ τ' *
          intervalIntegral.orderedSimplexIntegral
            (Finset.univ : Finset (Fin n)).card β
            (d.1.interactionComponentShuffleIntegrand shuffle
              (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
                d.1.canonicalComponentInteractionShuffle)) := by
      apply Fintype.sum_congr
      intro shuffle
      exact (d.externalSign_mul_orderedSimplexIntegral_componentShuffle_eq_relabelDysonAmplitude
        ε β g τ τ' shuffle).symm
    _ = twoPointExternalOrderSign τ τ' *
        ∑ shuffle : d.1.ComponentInteractionShuffle,
          intervalIntegral.orderedSimplexIntegral
            (Finset.univ : Finset (Fin n)).card β
            (d.1.interactionComponentShuffleIntegrand shuffle
              (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
                d.1.canonicalComponentInteractionShuffle)) := by
      rw [Finset.mul_sum]
    _ = twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          intervalIntegral.orderedSimplexIntegral
            (d.1.interactionComponentSize B) β
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle B) := by
      rw [d.sum_componentInteractionShuffle_orderedSimplexIntegral_mixedComponentDysonLocalIntegrand_eq_prod
        ε β g τ τ' d.1.canonicalComponentInteractionShuffle]

end Fermionic
end SecondQuantization
