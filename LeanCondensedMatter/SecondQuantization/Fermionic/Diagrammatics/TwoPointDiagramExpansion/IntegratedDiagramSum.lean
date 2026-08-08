import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableFiniteSum
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityCast
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentShuffleIntegrability
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCanonicalLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonIntegral

set_option linter.style.header false

/-!
# Integrating the finite two-point diagram sum

The individual fixed-diagram integrands are only piecewise continuous, but the component-local
regularity theory proves they are measurable and locally bounded.  Hence the finite Wick-diagram sum
may now be commuted with the recursive ordered-simplex integral.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The Dyson-signed fixed-time amplitude of every fixed-external diagram is measurable and locally
bounded on finite interaction-time cubes. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
  let hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hprod := d.1.measurableLocallyBounded_interactionComponentShuffleIntegrand
    d.1.canonicalComponentInteractionShuffle
    (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
      d.1.canonicalComponentInteractionShuffle)
    (fun B => d.measurableLocallyBounded_mixedComponentDysonLocalIntegrand
      ε β g τ τ' d.1.canonicalComponentInteractionShuffle B)
  have hcast := hprod.finCast hcard
  have hscaled := hcast.const_mul (twoPointExternalOrderSign τ τ')
  have heq :
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) =
        fun σ => twoPointExternalOrderSign τ τ' *
          d.1.interactionComponentShuffleIntegrand
            d.1.canonicalComponentInteractionShuffle
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle)
            (fun k => σ (Fin.cast hcard k)) := by
    funext σ
    rw [d.dysonFixedTimeAmplitude_eq_canonicalComponentShuffleIntegrand]
    rfl
  rw [heq]
  exact hscaled

/-- The integrated order-`n` two-point coefficient is exactly the finite sum of the integrated
fixed-diagram Dyson amplitudes. -/
theorem twoPointDiagramCoefficient_eq_sum_dysonAmplitude
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        d.dysonAmplitude ε β g τ τ' := by
  unfold twoPointDiagramCoefficient twoPointDiagramIntegrand
  rw [← intervalIntegral.orderedSimplexIntegral_smul]
  calc
    intervalIntegral.orderedSimplexIntegral n β
        (fun σ => (-1 : ℂ) ^ n *
          ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
            d.fixedTimeAmplitude ε β g τ τ' σ) =
      intervalIntegral.orderedSimplexIntegral n β
        (fun σ => ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
          d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
        apply intervalIntegral.orderedSimplexIntegral_congr
        intro σ
        rw [Finset.mul_sum]
        rfl
    _ = ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        intervalIntegral.orderedSimplexIntegral n β
          (fun σ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
        exact intervalIntegral.orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded
          (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)) n β
          (fun d σ => d.dysonFixedTimeAmplitude ε β g τ τ' σ)
          (fun d _ => d.measurableLocallyBounded_dysonFixedTimeAmplitude
            ε β g τ τ')
    _ = ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        d.dysonAmplitude ε β g τ τ' := by
        apply Finset.sum_congr rfl
        intro d _
        exact (d.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude
          ε β g τ τ').symm

end Fermionic
end SecondQuantization
