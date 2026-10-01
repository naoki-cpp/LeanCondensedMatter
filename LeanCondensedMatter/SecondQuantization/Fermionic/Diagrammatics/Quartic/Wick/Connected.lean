import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.AmplitudeFactorization

set_option linter.style.header false

/-!
# Connected fermionic quartic Wick diagrams

Packages the fermionic quartic Wick amplitude as a multiplicative weight on the shared quartic
connected decomposition. This exposes the corresponding normalized diagram moment and cumulant
independently of the Dyson linked-cluster endpoint.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- The fermionic quartic Wick amplitude as a multiplicative weight on the shared connected
quartic-diagram decomposition. -/
noncomputable def quarticWickDiagramMultiplicativeWeight
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ :=
  Common.QuarticDiagram.multiplicativeWeight
    (N := N)
    (fun d => quarticWickDiagramAmplitude ε β g d)
    (fun d => quarticWickDiagramAmplitude_eq_prod_components ε β g d)

/-- Total fermionic quartic Wick-diagram weight on a finite vertex set, bundled with its canonical
empty-set normalization. -/
noncomputable def quarticWickDiagramMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticWickDiagramMultiplicativeWeight (N := N) ε β g).normalizedObjectMoment

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
