import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Ordered-simplex two-point Wick expansion

This module integrates the fixed-time external-leg Wick expansion over the ordered simplex of
interaction times and includes the Dyson sign `(-1)^n`.

The finite diagram sum remains inside `orderedSimplexIntegral`. This is deliberate: mixed time
ordering is only piecewise continuous when an interaction time crosses an external time, so
commuting the integral with the finite diagram sum requires a separate integrability argument.
The theorem here does not assume that later analytic step.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The order-`n` interaction integrand of the unnormalized two-point numerator, written as a sum
over slot-indexed quartic vertex labels. -/
noncomputable def twoPointDysonOrderIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ∑ q : Fin n → QuarticVertexLabel Mode,
    orderedTwoPointVertexWeight g q *
      Common.finiteGibbsExpectation (fermionEnergy ε) β
        (mixedTimeOrderedVertexComp ε i j τ τ' q σ)

/-- The same order-`n` integrand, written as a sum over fixed-external two-point Wick diagrams. -/
noncomputable def twoPointWickDiagramOrderIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
    d.fixedTimeAmplitude ε β g τ τ' σ

/-- At every interaction-time assignment, the diagram integrand is the mixed time-ordered
interaction integrand. -/
theorem twoPointWickDiagramOrderIntegrand_eq_twoPointDysonOrderIntegrand {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    twoPointWickDiagramOrderIntegrand ε β g i j τ τ' σ =
      twoPointDysonOrderIntegrand ε β g i j τ τ' σ := by
  exact sum_fixedExternalTwoPointWickDiagram_fixedTimeAmplitude_eq_sum_vertexLabel_expectation
    ε β g i j τ τ' σ

/-- The order-`n` coefficient of the unnormalized imaginary-time two-point numerator. The two
external fields are time ordered together with the `n` quartic interaction vertices. -/
noncomputable def twoPointDysonOrderCoefficient (n : ℕ)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (twoPointDysonOrderIntegrand ε β g i j τ τ')

/-- The order-`n` two-point Wick-diagram coefficient, with the diagram sum retained inside the
ordered-simplex integral. -/
noncomputable def twoPointWickDiagramOrderCoefficient (n : ℕ)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (twoPointWickDiagramOrderIntegrand ε β g i j τ τ')

/-- The complete order-`n` external-leg Wick expansion: the ordered-simplex diagram coefficient
is the corresponding mixed time-ordered perturbative coefficient. -/
theorem twoPointWickDiagramOrderCoefficient_eq_twoPointDysonOrderCoefficient (n : ℕ)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointWickDiagramOrderCoefficient n ε β g i j τ τ' =
      twoPointDysonOrderCoefficient n ε β g i j τ τ' := by
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact twoPointWickDiagramOrderIntegrand_eq_twoPointDysonOrderIntegrand
    ε β g i j τ τ' σ

/-- Canonical direction of the order-`n` two-point Wick expansion. -/
theorem twoPointDysonOrderCoefficient_eq_twoPointWickDiagramOrderCoefficient (n : ℕ)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonOrderCoefficient n ε β g i j τ τ' =
      twoPointWickDiagramOrderCoefficient n ε β g i j τ τ' :=
  (twoPointWickDiagramOrderCoefficient_eq_twoPointDysonOrderCoefficient
    n ε β g i j τ τ').symm

/-- Density-state form of the order-`n` external-leg Wick expansion. -/
theorem twoPointWickDiagramOrderCoefficient_eq_densityExpectation (n : ℕ)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointWickDiagramOrderCoefficient n ε β g i j τ τ' =
      (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
        (fun σ => ∑ q : Fin n → QuarticVertexLabel Mode,
          orderedTwoPointVertexWeight g q *
            (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperator
                (mixedTimeOrderedVertexComp ε i j τ τ' q σ))) := by
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact
    sum_fixedExternalTwoPointWickDiagram_fixedTimeAmplitude_eq_sum_vertexLabel_densityExpectation
      ε β g i j τ τ' σ

end Fermionic
end SecondQuantization
