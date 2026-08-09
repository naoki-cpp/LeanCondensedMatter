import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude

set_option linter.style.header false

/-!
# Interaction relabeling between two vertex orders

Two explicit presentations of the same finite-set fixed-external diagram differ only by the
interaction-slot permutation carrying the second vertex order to the first.  This lets the LCT use
the already proved injective-time/integrated relabel covariance when the global vertex-order sum is
reindexed by component-local orders and a component shuffle.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The flattened interaction-slot relabeling taking the second ordered presentation to the first,
followed by the first ordered-to-ambient leg map, is the second ordered-to-ambient leg map. -/
theorem interactionVertexPositionRelabel_orderChange
    {S : Finset (Fin N)} (order₁ order₂ : Common.QuarticVertexOrder S) :
    (interactionVertexPositionRelabel (order₂.trans order₁.symm)).trans
        (Common.orderedTwoPointLegToDiagramLeg order₁) =
      Common.orderedTwoPointLegToDiagramLeg order₂ := by
  apply Equiv.ext
  intro p
  unfold interactionVertexPositionRelabel Common.orderedTwoPointLegToDiagramLeg
  simp only [Equiv.trans_apply]
  generalize
      Common.twoPointLegEquiv (Finset.univ : Finset (Fin S.card)))
        ((finCongr (by simp)) p) = leg
  rcases leg with e | ⟨v, l⟩
  · rfl
  · simp [interactionVertexLegRelabel, Common.twoPointInteractionOrderLegEquiv]

/-- Reindexing the same arbitrary-set fixed-external diagram by two interaction orders gives explicit
diagrams related by the corresponding interaction-slot permutation. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_relabel_orderChange
    {S : Finset (Fin N)} (i j : Mode)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j)
    (order₁ order₂ : Common.QuarticVertexOrder S) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order₁ d).relabelInteractionVertices
        (order₂.trans order₁.symm) =
      fixedExternalTwoPointWickDiagramOrderEquiv i j order₂ d := by
  apply Subtype.ext
  apply Common.TwoPointDiagram.ext
  · simp [FixedExternalTwoPointWickDiagram.relabelInteractionVertices,
      fixedExternalTwoPointWickDiagramOrderEquiv_val]
  · funext v
    change d.1.vertexLabel (order₁ ((order₂.trans order₁.symm) v.1)) =
      d.1.vertexLabel (order₂ v.1)
    simp
  · rw [fixedExternalTwoPointWickDiagramOrderEquiv_val,
      fixedExternalTwoPointWickDiagramOrderEquiv_val]
    unfold FixedExternalTwoPointWickDiagram.relabelInteractionVertices
    unfold Common.TwoPointDiagram.inInteractionOrder
    change (Equiv.cast _ (d.1.pairingInInteractionOrder order₁)).relabel
        (interactionVertexPositionRelabel (order₂.trans order₁.symm)) =
      Equiv.cast _ (d.1.pairingInInteractionOrder order₂)
    unfold Common.TwoPointDiagram.pairingInInteractionOrder
    rw [Pairing.relabel_trans]
    rw [interactionVertexPositionRelabel_orderChange]

end Fermionic
end SecondQuantization
