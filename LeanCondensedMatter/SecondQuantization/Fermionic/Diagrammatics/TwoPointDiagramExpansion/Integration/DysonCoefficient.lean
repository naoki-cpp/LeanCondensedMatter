import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Amplitude
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Ordered-simplex two-point Dyson coefficients

This module integrates the fixed-time external-leg Wick expansion over the ordered simplex and
attaches the `(-1)^n` Dyson sign. The operator presentation uses the canonical free Gibbs density
state directly; no parallel finite-Gibbs coefficient API is maintained.

The unconditional public theorem integrates the pointwise finite sum over diagrams.  Commuting that
finite diagram sum with the ordered-simplex integral is a separate analytic obligation, because
mixed time ordering changes when an interaction time crosses an external time and no individual
diagram amplitude is continuous.  It is discharged under measurable local boundedness in
`DiagramSumIntegral.lean` by `twoPointDiagramCoefficient_eq_sum_dysonAmplitude`.
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

/-- The canonical order-`n` perturbative two-point coefficient in the density-state operator
presentation. -/
noncomputable def twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (fun σ =>
      ∑ q : Fin n → QuarticVertexLabel Mode,
        orderedTwoPointVertexWeight g q *
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperator
              (mixedTimeOrderedVertexComp ε i j τ τ' q σ)))

/-- The ordered-simplex external-leg diagram coefficient equals the mixed time-ordered Dyson
coefficient at every perturbation order. -/
theorem twoPointDiagramCoefficient_eq_twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      twoPointDysonCoefficient (n := n) ε β g i j τ τ' := by
  unfold twoPointDiagramCoefficient twoPointDysonCoefficient
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  unfold twoPointDiagramIntegrand
  have hsum :
      (∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
          d.fixedTimeAmplitude ε β g τ τ' σ) =
        twoPointExternalOrderSign τ τ' *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            orderedTwoPointVertexWeight g q *
              ∑ pairing : Pairing (2 * n + 1),
                orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
    calc
      (∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
          d.fixedTimeAmplitude ε β g τ τ' σ) =
        ∑ x : OrderedTwoPointWickDiagramData Mode n,
          orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ x := by
        simpa [FixedExternalTwoPointWickDiagram.fixedTimeAmplitude] using
          (Equiv.sum_comp
            (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ)
            (orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ))
      _ = ∑ q : Fin n → QuarticVertexLabel Mode,
          ∑ pairing : Pairing (2 * n + 1),
            orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ (q, pairing) :=
        Fintype.sum_prod_type _
      _ = ∑ q : Fin n → QuarticVertexLabel Mode,
          (twoPointExternalOrderSign τ τ' * orderedTwoPointVertexWeight g q) *
            ∑ pairing : Pairing (2 * n + 1),
              orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pairing _
        rfl
      _ = twoPointExternalOrderSign τ τ' *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            orderedTwoPointVertexWeight g q *
              ∑ pairing : Pairing (2 * n + 1),
                orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue]
  ring

end Fermionic
end SecondQuantization
