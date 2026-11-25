import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Amplitude
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.PairContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Integral

set_option linter.style.header false

/-!
# Scalar two-point diagram integrals

Integrate one fixed-external diagram or the pointwise finite diagram sum, and
attach the Dyson sign. Identifying these coefficients with the operator
presentation belongs to DysonCoefficient; interchanging the finite diagram sum
and the integral requires the separate regularity proof in DiagramSumIntegral.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The pointwise sum of fixed-time amplitudes over diagrams with the external labels fixed to
`Tτ cᵢ(τ) cⱼ†(τ')`. -/
noncomputable def twoPointDiagramIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
    d.fixedTimeAmplitude ε β g τ τ' σ

/-- Ordered-simplex contribution of one fixed-external diagram, before the Dyson sign. -/
noncomputable def FixedExternalTwoPointWickDiagram.orderedSimplexContribution
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ => d.fixedTimeAmplitude ε β g τ τ' σ)

/-- Integrated amplitude of one fixed-external diagram, including the order-`n` Dyson sign. -/
noncomputable def FixedExternalTwoPointWickDiagram.dysonAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.orderedSimplexContribution ε β g τ τ'

/-- The order-`n` coefficient obtained by integrating the pointwise external-leg diagram sum. -/
noncomputable def twoPointDiagramCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (twoPointDiagramIntegrand ε β g i j τ τ')

open Common in
/-- The actual fixed-time amplitude of a two-point Wick diagram equals the
general external-insertion amplitude after transporting its fixed-leg pairing.
Both oriented contractions live at exactly the same mixed positions, even
at coincident times. -/
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_eq_externalInsertion
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.fixedTimeAmplitude ε β g τ τ' σ =
      ExternalInsertionWickDiagram.fixedTimeAmplitude
        (twoPointDiagramExternalInsertionEquiv Finset.univ d.1) ε β g
        (twoPointExternalTimes τ τ') σ := by
  classical
  let D := twoPointDiagramExternalInsertionEquiv Finset.univ d.1
  have hlabel : D.externalLabel = twoPointExternalLabels i j := d.2
  have hvertex : D.vertexLabelSequence = d.vertexLabelSequence := rfl
  have hweight : D.vertexWeight g = orderedTwoPointVertexWeight g d.vertexLabelSequence := by
    unfold ExternalInsertionDiagram.vertexWeight orderedTwoPointVertexWeight
    rw [← hvertex]
    exact (Equiv.prod_comp
      (Equiv.ofBijective (fun v : Fin n => (⟨v, Finset.mem_univ v⟩ :
        ↥(Finset.univ : Finset (Fin n)))) ⟨fun a b h => congrArg Subtype.val h,
          fun v => ⟨v.1, Subtype.ext rfl⟩⟩)
      (fun v => g (D.vertexLabel v))).symm
  change orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ
      (d.vertexLabelSequence, d.1.pairingInMixedOrder τ τ' σ) =
    ExternalInsertionWickDiagram.fixedTimeAmplitude D ε β g
      (twoPointExternalTimes τ τ') σ
  unfold orderedTwoPointFixedTimeAmplitude ExternalInsertionWickDiagram.fixedTimeAmplitude
    orderedTwoPointPairingValue ExternalInsertionWickDiagram.mixedPairingValue
    mixedTimeOrderedAtomicPairValue externalInsertionMixedTimeOrderedAtomicPairValue
  rw [externalInsertionMixedAtomicOrderSign_twoPoint, hweight,
    show D.pairingInMixedOrder (twoPointExternalTimes τ τ') σ =
      d.1.pairingInMixedOrder τ τ' σ from
        twoPointDiagramExternalInsertionEquiv_pairingInMixedOrder d.1 τ τ' σ,
    hlabel, hvertex, mixedTimeOrderedAtomicFieldFamily_eq_externalInsertion]

open Common in
/-- The same diagram transport preserves the integrated Dyson amplitude
without any sign restriction on the integration endpoint β. -/
theorem FixedExternalTwoPointWickDiagram.dysonAmplitude_eq_externalInsertion
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    d.dysonAmplitude ε β g τ τ' =
      ExternalInsertionWickDiagram.dysonAmplitude
        (twoPointDiagramExternalInsertionEquiv Finset.univ d.1) ε β g
        (twoPointExternalTimes τ τ') := by
  unfold FixedExternalTwoPointWickDiagram.dysonAmplitude
    ExternalInsertionWickDiagram.dysonAmplitude
    FixedExternalTwoPointWickDiagram.orderedSimplexContribution
    ExternalInsertionWickDiagram.orderedSimplexContribution
  congr 1
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact d.fixedTimeAmplitude_eq_externalInsertion ε β g τ τ' σ

end Fermionic
end SecondQuantization
