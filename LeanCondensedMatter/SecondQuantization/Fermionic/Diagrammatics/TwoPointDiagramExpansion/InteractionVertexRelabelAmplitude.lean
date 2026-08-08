import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Amplitude factors under interaction-vertex relabeling

Interaction-vertex relabeling permutes the slot-indexed quartic labels. The product of quartic
couplings is therefore invariant. This removes the algebraic vertex-weight factor from the
remaining fixed-time amplitude covariance problem, leaving only the mixed-time pairing value and
its time-order transport.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- The product of quartic vertex weights is invariant under a permutation of interaction slots. -/
theorem orderedTwoPointVertexWeight_comp_perm
    {n : ℕ} (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (π : Equiv.Perm (Fin n)) :
    orderedTwoPointVertexWeight g (fun v => q (π v)) =
      orderedTwoPointVertexWeight g q := by
  unfold orderedTwoPointVertexWeight
  exact Equiv.prod_comp π (fun v => g (q v))

/-- Relabeling interaction vertices does not change the product of quartic coupling weights. -/
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_vertexWeight
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) (π : Equiv.Perm (Fin n)) :
    orderedTwoPointVertexWeight g
        (d.relabelInteractionVertices π).vertexLabelSequence =
      orderedTwoPointVertexWeight g d.vertexLabelSequence := by
  rw [show (d.relabelInteractionVertices π).vertexLabelSequence =
      fun v => d.vertexLabelSequence (π v) by
    funext v
    exact d.relabelInteractionVertices_vertexLabelSequence π v]
  exact orderedTwoPointVertexWeight_comp_perm g d.vertexLabelSequence π

end Fermionic
end SecondQuantization
