import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderSignature
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossingTimeLocality
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.PairContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Chamber regularity, measurability, and ordered-simplex integration of the diagram sum

The public order-`n` coefficient integrates the pointwise sum over diagrams, whereas every
factorization statement is phrased for the integrated amplitude of a single diagram. Exchanging the
two requires integrability of each summand, and the summands are only chamberwise continuous: the
mixed time order changes when an interaction time crosses an external time.

This module owns the continuous chamber representatives of mixed-component factors, then uses the
Common-owned `TwoPointOrderSignature` finite measurable partition to upgrade chamberwise continuity
to global measurability. Measurable local boundedness then provides exactly the regularity needed to
commute the finite diagram sum with the ordered-simplex integral.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Continuous chamber representative of the Dyson-signed component fixed-time value. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    (Fin n → ℝ) → ℂ :=
  fun σ => d.mixedComponentDysonSign B *
    (d.mixedComponentVertexWeight g B *
      (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ₀ B *
        ∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
          orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2)))

/-- The Dyson-signed chamber representative is globally continuous. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentDysonFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
  exact continuous_const.mul
    (continuous_const.mul
      (continuous_const.mul
        (continuous_finsetProd _ fun pr _ =>
          continuous_orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2))))

/-- On the base chamber, the Dyson-signed representative agrees with the actual component factor. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ₀ σ) :
    d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B σ =
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
  classical
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
    FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
    FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
    FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
  apply congrArg (fun z : ℂ =>
    d.mixedComponentDysonSign B * (d.mixedComponentVertexWeight g B * z))
  rw [d.1.mixedComponentWeight_eq_of_sameOrderChamber
    Common.Statistics.fermion τ τ' σ₀ σ B hChamber]
  apply congrArg (fun z : ℂ =>
    d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B * z)
  let e := d.1.mixedComponentPairTimeEquiv τ τ' σ₀ σ B
  calc
    (∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
        orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2)) =
      ∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
        d.mixedPairContractionValue ε β τ τ' σ (e pr).1 := by
      apply Fintype.prod_congr
      intro pr
      have hLegs :=
        d.1.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
          τ τ' σ₀ σ B hChamber pr
      rw [d.mixedPairContractionValue_eq_orderedTwoPointLegPairContraction]
      rw [hLegs.1, hLegs.2]
    _ = ∏ q : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ q.1 := by
      exact Equiv.prod_comp e
        (fun q : d.1.MixedComponentPair τ τ' σ B =>
          d.mixedPairContractionValue ε β τ τ' σ q.1)

/-- A mixed-component Dyson fixed-time value is globally measurable after assembling its finite
chamberwise-continuous representatives along the mixed-order signature partition. -/
theorem FixedExternalTwoPointWickDiagram.measurable_mixedComponentDysonFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) :
    Measurable (fun σ : Fin n → ℝ =>
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) := by
  classical
  let rep : (Fin n → ℝ) → ℂ := fun σ =>
    ∑ s : TwoPointOrderSignature n,
      if twoPointOrderSignature τ τ' σ = s then
        d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s) B σ
      else 0
  have hRep : Measurable rep := by
    dsimp [rep]
    apply Finset.measurable_sum
    intro s _
    have hFiber := measurableSet_twoPointOrderSignatureFiber τ τ' s
    have hContinuous :=
      (d.continuous_mixedComponentDysonFixedTimeChamberRepresentative
        ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) B).measurable
    simpa only [twoPointOrderSignatureFiber, Set.mem_setOf_eq] using
      (Measurable.ite hFiber hContinuous measurable_const)
  have hEq : rep = fun σ : Fin n → ℝ =>
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
    funext σ
    dsimp [rep]
    let s₀ := twoPointOrderSignature τ τ' σ
    have hsum :
        (∑ s : TwoPointOrderSignature n,
          if twoPointOrderSignature τ τ' σ = s then
            d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
              (twoPointOrderSignatureBase τ τ' s) B σ
          else 0) =
        d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s₀) B σ := by
      change (∑ s : TwoPointOrderSignature n,
          if s₀ = s then
            d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
              (twoPointOrderSignatureBase τ τ' s) B σ
          else 0) =
        d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s₀) B σ
      simp
    rw [hsum]
    exact d.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
      ε β g τ τ'
      (twoPointOrderSignatureBase τ τ' s₀) σ B
      (by simpa [s₀] using sameTwoPointOrderChamber_signatureBase τ τ' σ)
  rw [← hEq]
  exact hRep

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
        fun B _ => by
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
            exact
              (d.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
                ε β g τ τ' (twoPointOrderSignatureBase τ τ'
                  (twoPointOrderSignature τ τ' σ)) σ B
                (sameTwoPointOrderChamber_signatureBase τ τ' σ)).symm)
  have heq : (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) =
      fun σ : Fin n → ℝ =>
        twoPointExternalOrderSign τ τ' *
          ∏ B : d.1.componentPartition.parts,
            d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
    funext σ
    exact d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components ε β g τ τ' σ
  rw [heq]
  exact hprod

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
