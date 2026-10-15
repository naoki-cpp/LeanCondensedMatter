import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Amplitude
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

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

end Fermionic
end SecondQuantization
