import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Ordered-simplex two-point Dyson coefficients

This module integrates the fixed-time external-leg Wick expansion over the ordered simplex and
attaches the `(-1)^n` Dyson sign.

The unconditional public theorem integrates the pointwise finite sum over diagrams.  It deliberately
does not yet commute that finite diagram sum with the ordered-simplex integral: mixed time ordering
changes when an interaction time crosses an external time, so continuity or piecewise-integrability
of each individual diagram amplitude is a separate analytic obligation.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The pointwise sum of fixed-time amplitudes over diagrams with the external labels fixed to
`Tτ cᵢ(τ) cⱼ†(τ')`. -/
noncomputable def twoPointDiagramIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
    d.fixedTimeAmplitude ε β g τ τ' σ

/-- The coupling-weighted mixed time-ordered finite Gibbs expectation at fixed interaction times. -/
noncomputable def twoPointDysonIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ∑ q : Fin n → QuarticVertexLabel Mode,
    orderedTwoPointVertexWeight g q *
      Common.finiteGibbsExpectation (fermionEnergy ε) β
        (mixedTimeOrderedVertexComp ε i j τ τ' q σ)

/-- Pointwise, the external-leg diagram integrand is the coupling-weighted mixed time-ordered
finite Gibbs expectation. -/
theorem twoPointDiagramIntegrand_eq_twoPointDysonIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    twoPointDiagramIntegrand ε β g i j τ τ' σ =
      twoPointDysonIntegrand ε β g i j τ τ' σ := by
  exact sum_fixedExternalTwoPointWickDiagram_fixedTimeAmplitude_eq_sum_vertexLabel_expectation
    ε β g i j τ τ' σ

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

/-- The order-`n` perturbative two-point coefficient in the vertex-label/operator presentation. -/
noncomputable def twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (twoPointDysonIntegrand ε β g i j τ τ')

/-- The ordered-simplex external-leg diagram coefficient equals the mixed time-ordered Dyson
coefficient at every perturbation order. -/
theorem twoPointDiagramCoefficient_eq_twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient ε β g i j τ τ' =
      twoPointDysonCoefficient ε β g i j τ τ' := by
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact twoPointDiagramIntegrand_eq_twoPointDysonIntegrand ε β g i j τ τ' σ

/-- Density-state form of the fixed-time Dyson integrand. -/
noncomputable def twoPointDensityDysonIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ∑ q : Fin n → QuarticVertexLabel Mode,
    orderedTwoPointVertexWeight g q *
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          (mixedTimeOrderedVertexComp ε i j τ τ' q σ))

/-- The finite Gibbs and density-state Dyson integrands agree pointwise. -/
theorem twoPointDensityDysonIntegrand_eq_twoPointDysonIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    twoPointDensityDysonIntegrand ε β g i j τ τ' σ =
      twoPointDysonIntegrand ε β g i j τ τ' σ := by
  simp only [twoPointDensityDysonIntegrand, twoPointDysonIntegrand,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]

/-- Density-state presentation of the order-`n` perturbative two-point coefficient. -/
noncomputable def twoPointDensityDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (twoPointDensityDysonIntegrand ε β g i j τ τ')

/-- The density-state and finite Gibbs presentations of the two-point Dyson coefficient agree. -/
theorem twoPointDensityDysonCoefficient_eq_twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDensityDysonCoefficient ε β g i j τ τ' =
      twoPointDysonCoefficient ε β g i j τ τ' := by
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact twoPointDensityDysonIntegrand_eq_twoPointDysonIntegrand ε β g i j τ τ' σ

/-- The integrated external-leg diagram coefficient also has the canonical density-state form. -/
theorem twoPointDiagramCoefficient_eq_twoPointDensityDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient ε β g i j τ τ' =
      twoPointDensityDysonCoefficient ε β g i j τ τ' := by
  rw [twoPointDiagramCoefficient_eq_twoPointDysonCoefficient,
    twoPointDensityDysonCoefficient_eq_twoPointDysonCoefficient]

end Fermionic
end SecondQuantization
