import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Connected

set_option linter.style.header false

/-!
# Fermionic quartic Wick cumulants

Adds the Möbius-inversion layer on top of the forward-only fermionic Wick diagram moment API.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Fermionic quartic Wick-diagram cumulant in normalized finite-set coordinates. -/
noncomputable def quarticWickDiagramCumulant
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticWickDiagramMoment (N := N) ε β g).cumulant

/-- The fermionic quartic Wick-diagram cumulant is exactly the sum of amplitudes of connected
quartic Wick diagrams. -/
theorem quarticWickDiagramCumulant_eq_sum_connectedQuarticWickDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    quarticWickDiagramCumulant (N := N) ε β g S =
      ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
  let W := quarticWickDiagramMultiplicativeWeight (N := N) ε β g
  change W.normalizedObjectMoment.cumulant S =
    ∑ d : ConnectedQuarticWickDiagram Mode N S,
      quarticWickDiagramAmplitude ε β g d.1
  calc
    W.normalizedObjectMoment.cumulant S = W.connectedContribution S :=
      W.normalizedObjectMoment_cumulant_eq_connectedContribution hS
    _ = ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := rfl

end
end Fermionic
end SecondQuantization
