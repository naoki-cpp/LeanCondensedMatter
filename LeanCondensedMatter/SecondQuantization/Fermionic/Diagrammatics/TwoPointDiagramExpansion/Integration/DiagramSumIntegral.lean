import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity

set_option linter.style.header false

/-!
# Ordered-simplex integration of the two-point diagram sum

This module owns the bridge from the public order-`n` coefficient, defined as an ordered-simplex
integral of the pointwise diagram sum, to the finite sum of per-diagram integrated amplitudes.
The required measurable local boundedness of individual amplitudes follows from the general
external-insertion chamber theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The signed pointwise amplitude of one diagram is measurably locally bounded. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
  let D := twoPointDiagramExternalInsertionEquiv Finset.univ d.1
  have heq : (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) =
      fun σ : Fin n → ℝ =>
        ExternalInsertionWickDiagram.dysonFixedTimeAmplitude D ε β g
          (twoPointExternalTimes τ τ') σ := by
    funext σ
    unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    rw [d.fixedTimeAmplitude_eq_externalInsertion]
  rw [heq]
  exact ExternalInsertionWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    D ε β g (twoPointExternalTimes τ τ')

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
