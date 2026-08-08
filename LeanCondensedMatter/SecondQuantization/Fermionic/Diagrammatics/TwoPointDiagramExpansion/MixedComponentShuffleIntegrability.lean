import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplexMeasurable
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentIntegrability

set_option linter.style.header false

/-!
# Measurable bounded shuffle identity for localized mixed component factors

The actual localized component factors are finite measurable selections of globally continuous
fixed-signature representatives.  Hence they satisfy the measurable-local-boundedness interface of
the generalized ordered-simplex shuffle theorem, with no global continuity assumption on the raw
factor across mixed-order walls.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Every canonical localized Dyson-signed component factor satisfies the reusable measurable local
boundedness interface required by the generalized ordered-simplex shuffle theorem. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_mixedComponentDysonLocalIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    intervalIntegral.MeasurableLocallyBounded
      (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B) := by
  apply intervalIntegral.measurableLocallyBounded_of_finite_continuous_selection
    (g := fun s : TwoPointOrderSignature n =>
      d.mixedComponentDysonLocalChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s) shuffle B)
  · exact d.measurable_mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B
  · intro s
    exact d.continuous_mixedComponentDysonLocalChamberRepresentative
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) shuffle B
  · intro localTime
    exact d.exists_mixedComponentDysonLocalChamberRepresentative_eq
      ε β g τ τ' shuffle B localTime

/-- The complete Dyson-signed fixed-diagram integrand is globally measurable and locally bounded,
even though it can change chamber formula when an interaction time crosses an external time. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
  let branch : TwoPointOrderSignature n → (Fin n → ℝ) → ℂ := fun s σ =>
    twoPointExternalOrderSign τ τ' *
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s) B σ
  apply intervalIntegral.measurableLocallyBounded_of_finite_continuous_selection
    (g := branch)
  · have hMeas : Measurable (fun σ : Fin n → ℝ =>
        twoPointExternalOrderSign τ τ' *
          ∏ B : d.1.componentPartition.parts,
            d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) := by
      exact measurable_const.mul
        (Finset.measurable_prod _ fun B _ =>
          d.measurable_mixedComponentDysonFixedTimeValue ε β g τ τ' B)
    have hEq : (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) =
        fun σ => twoPointExternalOrderSign τ τ' *
          ∏ B : d.1.componentPartition.parts,
            d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
      funext σ
      exact d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components
        ε β g τ τ' σ
    rw [hEq]
    exact hMeas
  · intro s
    unfold branch
    exact continuous_const.mul
      (continuous_finsetProd _ fun B _ =>
        d.continuous_mixedComponentDysonFixedTimeChamberRepresentative
          ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) B)
  · intro σ
    let s := twoPointOrderSignature τ τ' σ
    refine ⟨s, ?_⟩
    rw [d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components]
    apply congrArg (fun z : ℂ => twoPointExternalOrderSign τ τ' * z)
    apply Fintype.prod_congr
    intro B
    exact (d.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) σ B
      (by simpa [s] using sameTwoPointOrderChamber_signatureBase τ τ' σ)).symm

/-- The localized signed component integrands satisfy the finite-family ordered-simplex shuffle
product identity with no externally supplied continuity assumption. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentInteractionShuffle_orderedSimplexIntegral_mixedComponentDysonLocalIntegrand_eq_prod
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (baseShuffle : d.1.ComponentInteractionShuffle) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
      intervalIntegral.orderedSimplexIntegral
        (Finset.univ : Finset (Fin n)).card β
        (d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle))) =
      ∏ B : d.1.componentPartition.parts,
        intervalIntegral.orderedSimplexIntegral
          (d.1.interactionComponentSize B) β
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle B) := by
  exact d.1.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_prod_of_measurableLocallyBounded
    β (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle)
    (fun B => d.measurableLocallyBounded_mixedComponentDysonLocalIntegrand
      ε β g τ τ' baseShuffle B)

end Fermionic
end SecondQuantization
