import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentMeasurability

set_option linter.style.header false

/-!
# Commuting the diagram sum with the ordered-simplex integral

The public order-`n` coefficient integrates the pointwise sum over diagrams, whereas every
factorization statement is phrased for the integrated amplitude of a single diagram. Exchanging the
two requires integrability of each summand, and the summands are only chamberwise continuous: the
mixed time order changes when an interaction time crosses an external time.

Measurable local boundedness is exactly the regularity that survives those walls. Each signed
component factor has it, by the finite chamber-representative selection already used for the
component-local integrands; the full amplitude is a constant times a finite product of those
factors, so it has it too. The measurable finite-sum exchange then applies.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Every signed component fixed-time factor is measurably locally bounded: it is globally
measurable and agrees on each mixed-order chamber with a globally continuous representative. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_mixedComponentDysonFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) := by
  apply intervalIntegral.measurableLocallyBounded_of_finite_continuous_selection
    (g := fun s : TwoPointOrderSignature n =>
      d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s) B)
  · exact d.measurable_mixedComponentDysonFixedTimeValue ε β g τ τ' B
  · intro s
    exact d.continuous_mixedComponentDysonFixedTimeChamberRepresentative
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) B
  · intro σ
    refine ⟨twoPointOrderSignature τ τ' σ, ?_⟩
    exact (d.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' (twoPointOrderSignature τ τ' σ)) σ B
      (sameTwoPointOrderChamber_signatureBase τ τ' σ)).symm

/-- The signed pointwise amplitude of one diagram is measurably locally bounded. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
  have hprod :
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin n → ℝ =>
          twoPointExternalOrderSign τ τ' *
            ∏ B : d.1.componentPartition.parts,
              d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) :=
    (intervalIntegral.measurableLocallyBounded_const _).mul
      (intervalIntegral.MeasurableLocallyBounded.finsetProd Finset.univ
        (fun B σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B)
        fun B _ => d.measurableLocallyBounded_mixedComponentDysonFixedTimeValue ε β g τ τ' B)
  have heq : (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) =
      fun σ : Fin n → ℝ =>
        twoPointExternalOrderSign τ τ' *
          ∏ B : d.1.componentPartition.parts,
            d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
    funext σ
    exact d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components ε β g τ τ' σ
  rw [heq]
  exact hprod

/-- The unsigned pointwise amplitude of one diagram is measurably locally bounded. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_fixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.fixedTimeAmplitude ε β g τ τ' σ) := by
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

/-- **The order-`n` two-point coefficient is the sum of the integrated diagram amplitudes.**

This is the bridge from the public coefficient, defined as the ordered-simplex integral of the
pointwise diagram sum, to the per-diagram `dysonAmplitude` on which every component and
external/vacuum factorization is stated. -/
theorem twoPointDiagramCoefficient_eq_sum_dysonAmplitude {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      ∑ d : FixedExternalTwoPointWickDiagram Mode n i j, d.dysonAmplitude ε β g τ τ' := by
  unfold twoPointDiagramCoefficient twoPointDiagramIntegrand
  rw [intervalIntegral.orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded
    Finset.univ n β (fun d : FixedExternalTwoPointWickDiagram Mode n i j =>
      fun σ => d.fixedTimeAmplitude ε β g τ τ' σ)
    fun d _ => d.measurableLocallyBounded_fixedTimeAmplitude ε β g τ τ',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [FixedExternalTwoPointWickDiagram.dysonAmplitude,
    FixedExternalTwoPointWickDiagram.orderedSimplexContribution]

end Fermionic
end SecondQuantization
