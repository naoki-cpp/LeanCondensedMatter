import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Ordered-simplex input from component-local Dyson values

The global order-`n` Dyson sign is constant in the interaction times, so it can be moved inside the
ordered-simplex integral.  Combining this with the pointwise external/vacuum factorization gives the
factorized integrand that the subsequent shuffle/simplex decomposition must integrate.

This module deliberately stops before splitting the integral itself: proving that each component
factor depends only on its own local interaction-time coordinates is the next combinatorial and
analytic layer.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The integrated diagram amplitude is the ordered-simplex integral of the pointwise
Dyson-signed fixed-time amplitude. -/
theorem FixedExternalTwoPointWickDiagram.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    d.dysonAmplitude ε β g τ τ' =
      intervalIntegral.orderedSimplexIntegral n β
        (fun σ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
  change (-1 : ℂ) ^ n *
      intervalIntegral.orderedSimplexIntegral n β
        (fun σ => d.fixedTimeAmplitude ε β g τ τ' σ) =
    intervalIntegral.orderedSimplexIntegral n β
      (fun σ => (-1 : ℂ) ^ n * d.fixedTimeAmplitude ε β g τ τ' σ)
  exact (intervalIntegral.orderedSimplexIntegral_smul n β
    ((-1 : ℂ) ^ n) (fun σ => d.fixedTimeAmplitude ε β g τ τ' σ)).symm

/-- The integrated diagram amplitude with the external ordering sign and every signed component
factor displayed inside the ordered-simplex integral. -/
theorem FixedExternalTwoPointWickDiagram.dysonAmplitude_eq_orderedSimplexIntegral_externalSign_mul_prod_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    d.dysonAmplitude ε β g τ τ' =
      intervalIntegral.orderedSimplexIntegral n β (fun σ =>
        twoPointExternalOrderSign τ τ' *
          ∏ B : d.1.componentPartition.parts,
            d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) := by
  rw [d.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components ε β g τ τ' σ

/-- The integrated diagram amplitude with its signed external factor and signed vacuum factors
displayed inside the ordered-simplex integral.  This is the direct input to the next shuffle/product
identity. -/
theorem FixedExternalTwoPointWickDiagram.dysonAmplitude_eq_orderedSimplexIntegral_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    d.dysonAmplitude ε β g τ τ' =
      intervalIntegral.orderedSimplexIntegral n β (fun σ =>
        d.mixedExternalDysonFixedTimeValue ε β g τ τ' σ *
          d.1.vacuumComponentParts.prod
            (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ)) := by
  rw [d.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  exact d.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum ε β g τ τ' σ

end Fermionic
end SecondQuantization
