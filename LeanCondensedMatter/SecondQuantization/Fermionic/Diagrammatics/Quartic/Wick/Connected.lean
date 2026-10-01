import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.AmplitudeFactorization

set_option linter.style.header false

/-!
# Connected fermionic quartic Wick diagrams

Packages the fermionic quartic Wick amplitude as a multiplicative weight on the shared quartic
connected decomposition and exposes its normalized object moment. This layer uses only the forward
connected-decomposition theorem; Möbius inversion is kept in the separate cumulant layer.
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

/-- Total fermionic quartic Wick-diagram weight on a finite vertex set, bundled with its canonical
empty-set normalization. -/
noncomputable def quarticWickDiagramMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticWickDiagramMultiplicativeWeight (N := N) ε β g).normalizedObjectMoment

end
end Fermionic
end SecondQuantization
