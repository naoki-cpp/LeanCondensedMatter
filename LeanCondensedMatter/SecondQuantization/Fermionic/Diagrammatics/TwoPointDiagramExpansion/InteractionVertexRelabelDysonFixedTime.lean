import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelFixedTimeAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Dyson-signed fixed-time covariance under interaction-vertex relabeling

The fixed-time amplitude covariance already holds away from the interaction-time diagonals. Since
interaction-slot relabeling preserves the perturbation order, attaching the common order-`n` Dyson
sign preserves the same covariance.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The Dyson-signed fixed-time amplitude is covariant under interaction-slot relabeling whenever the
interaction-time assignment is injective. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.dysonFixedTimeAmplitude ε β g τ τ' (fun v => σ (π.symm v)) := by
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  rw [d.fixedTimeAmplitude_relabelInteractionVertices_of_injective
    π ε β g τ τ' σ hσ]

end Fermionic
end SecondQuantization
