import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion

set_option linter.style.header false

/-!
# Connected quartic Wick diagrams and Dyson vertex cumulants

The combinatorial connected-component decomposition is separated from the complex-valued Wick
amplitude. Their combination identifies the finite-set Dyson cumulant with the connected-diagram
amplitude sum. The decomposition adapter itself is statistics-independent and owned by `Common`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Multiplicative quartic Wick amplitude on the shared connected decomposition. -/
private noncomputable def quarticWickDiagramMultiplicativeWeight (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ where
  objectWeight d := quarticWickDiagramAmplitude ε β g d
  connectedWeight d := quarticWickDiagramAmplitude ε β g d.1
  weight_decompose d := by
    change quarticWickDiagramAmplitude ε β g d =
      ∏ B : d.componentPartition.parts,
        quarticWickDiagramAmplitude ε β g (d.restrictComponentConnected B.2).1
    exact quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected ε β g d

/-- The Dyson vertex cumulant is the sum of amplitudes of connected quartic Wick diagrams. -/
theorem dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    dysonVertexCumulant ε β (quarticInteraction g) S =
      ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
  let W := quarticWickDiagramMultiplicativeWeight (N := N) ε β g
  calc
    dysonVertexCumulant ε β (quarticInteraction g) S =
        Finpartition.cumulantFromMoment W.objectMoment S := by
      unfold dysonVertexCumulant
      congr 1
      funext T
      change dysonVertexMoment ε β (quarticInteraction g) T =
        ∑ d : QuarticWickDiagram Mode N T, quarticWickDiagramAmplitude ε β g d
      exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g T
    _ = W.connectedContribution S := W.cumulantFromMoment_objectMoment hS
    _ = ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
      rfl

end Fermionic
end SecondQuantization
