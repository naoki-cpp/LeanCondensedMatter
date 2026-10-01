import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Connected

set_option linter.style.header false

/-!
# Bosonic quartic thermal cumulants

Adds the Möbius-inversion layer on top of the forward-only bosonic thermal diagram moment API.
-/

namespace SecondQuantization
namespace Bosonic

open Combinatorics

noncomputable section

variable {Mode : Type*} [Fintype Mode] {N : ℕ}

/-- Coefficientwise bosonic thermal cumulant in normalized finite-set coordinates. -/
noncomputable def quarticThermalCumulant
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticThermalMoment (N := N) ε β g).cumulant

/-- The coefficientwise bosonic thermal cumulant is exactly the sum of order-averaged amplitudes of
connected quartic diagrams. -/
theorem quarticThermalCumulant_eq_sum_connectedQuarticDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    quarticThermalCumulant (N := N) ε β g S =
      ∑ d : Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S,
        QuarticDiagram.thermalAmplitude ε β g d.1 := by
  let W := quarticThermalDiagramMultiplicativeWeight (N := N) ε β g
  change W.normalizedObjectMoment.cumulant S =
    ∑ d : Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S,
      QuarticDiagram.thermalAmplitude ε β g d.1
  calc
    W.normalizedObjectMoment.cumulant S = W.connectedContribution S :=
      W.normalizedObjectMoment_cumulant_eq_connectedContribution hS
    _ = ∑ d : Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S,
        QuarticDiagram.thermalAmplitude ε β g d.1 := rfl

end
end Bosonic
end SecondQuantization
