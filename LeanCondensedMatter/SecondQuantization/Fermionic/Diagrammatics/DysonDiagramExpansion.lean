import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Connected

set_option linter.style.header false

/-!
# Fermionic Dyson-to-diagram expansion

Expansion of fermionic Dyson coefficients into Wick diagrams through flattened interaction legs,
free-Gibbs pairing evaluation, and canonical reindexing from pairings to labelled diagrams.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The factorial-normalized fermionic Dyson vertex moment is exactly the normalized total
quartic Wick-diagram moment. -/
theorem dysonVertexMomentSetFunction_eq_quarticWickDiagramMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} :
    dysonVertexMomentSetFunction (α := Fin N) ε β (quarticInteraction g) =
      quarticWickDiagramMoment (N := N) ε β g := by
  ext S
  change
    dysonVertexMoment ε β (quarticInteraction g) S =
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
  exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g S

end Fermionic
end SecondQuantization
