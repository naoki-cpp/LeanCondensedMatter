import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.AmplitudeFactorization

set_option linter.style.header false

/-!
# Connected fermionic quartic Wick diagrams

Packages the fermionic quartic Wick amplitude as a multiplicative weight on the shared quartic
connected decomposition. The normalized object moment is obtained directly from the generic
multiplicative-weight API; no fermionic-specific moment wrapper is needed.
-/

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


end
end Fermionic
end SecondQuantization
