import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Ordered-simplex input from Dyson-signed fixed-time amplitudes

The global order-`n` Dyson sign is constant in the interaction times, so it can be moved inside the
ordered-simplex integral.  This module exposes that bridge from the integrated diagram amplitude to
the pointwise Dyson-signed fixed-time amplitude; component factorization and shuffle/simplex
arguments remain in their downstream owners.
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

end Fermionic
end SecondQuantization
