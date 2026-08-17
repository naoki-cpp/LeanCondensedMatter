import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Analysis.DiagramRegularity

set_option linter.style.header false

/-!
# Ordered-simplex integration of the two-point diagram sum

This module owns the bridge from the public order-`n` coefficient, defined as an ordered-simplex
integral of the pointwise diagram sum, to the finite sum of per-diagram integrated amplitudes.
Regularity needed to exchange the finite sum and integral is owned by the Analysis layer.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The order-`n` two-point coefficient is the sum of the integrated diagram amplitudes.**

This is the bridge from the public coefficient, defined as the ordered-simplex integral of the
pointwise diagram sum, to the per-diagram `dysonAmplitude` on which every component and
external/vacuum factorization is stated. -/
theorem twoPointDiagramCoefficient_eq_sum_dysonAmplitude {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      ∑ d : FixedExternalTwoPointWickDiagram Mode n i j, d.dysonAmplitude ε β g τ τ' := by
  have hFixed : ∀ d : FixedExternalTwoPointWickDiagram Mode n i j,
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin n → ℝ => d.fixedTimeAmplitude ε β g τ τ' σ) := by
    intro d
    have hsign : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
      rw [← mul_pow]
      norm_num
    have heq : (fun σ : Fin n → ℝ => d.fixedTimeAmplitude ε β g τ τ' σ) =
        fun σ : Fin n → ℝ => (-1 : ℂ) ^ n * d.dysonFixedTimeAmplitude ε β g τ τ' σ := by
      funext σ
      unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
      rw [← mul_assoc, hsign, one_mul]
    rw [heq]
    exact (intervalIntegral.measurableLocallyBounded_const _).mul
      (d.measurableLocallyBounded_dysonFixedTimeAmplitude ε β g τ τ')
  unfold twoPointDiagramCoefficient twoPointDiagramIntegrand
  rw [intervalIntegral.orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded
    Finset.univ n β (fun d : FixedExternalTwoPointWickDiagram Mode n i j =>
      fun σ => d.fixedTimeAmplitude ε β g τ τ' σ)
    fun d _ => hFixed d,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [FixedExternalTwoPointWickDiagram.dysonAmplitude,
    FixedExternalTwoPointWickDiagram.orderedSimplexContribution]

end Fermionic
end SecondQuantization
