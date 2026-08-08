import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Interaction-order changes as slot relabelings

Changing the chosen order on an arbitrary finite interaction set only relabels the explicit `Fin n`
interaction slots.  This is the structural bridge from component-local order decompositions to the
existing interaction-relabel covariance theorem.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- The slot permutation carrying data expressed in `oldOrder` to data expressed in `newOrder`. -/
noncomputable def interactionOrderChange
    {S : Finset (Fin N)} (oldOrder newOrder : Common.QuarticVertexOrder S) :
    Equiv.Perm (Fin S.card) :=
  newOrder.trans oldOrder.symm

@[simp]
theorem interactionOrderChange_apply
    {S : Finset (Fin N)} (oldOrder newOrder : Common.QuarticVertexOrder S)
    (v : Fin S.card) :
    oldOrder (interactionOrderChange oldOrder newOrder v) = newOrder v := by
  simp [interactionOrderChange]

/-- The flattened interaction-slot relabel followed by the old order embedding is exactly the new
order embedding. -/
theorem interactionVertexPositionRelabel_trans_orderedTwoPointLegToDiagramLeg
    {S : Finset (Fin N)} (oldOrder newOrder : Common.QuarticVertexOrder S) :
    (interactionVertexPositionRelabel (interactionOrderChange oldOrder newOrder)).trans
        (Common.orderedTwoPointLegToDiagramLeg oldOrder) =
      Common.orderedTwoPointLegToDiagramLeg newOrder := by
  ext p
  apply (Common.twoPointLegEquiv S).injective
  rcases hleg : Common.twoPointLegEquiv
      (Finset.univ : Finset (Fin S.card)) p with e | ⟨v, l⟩
  · simp [interactionVertexPositionRelabel, Common.orderedTwoPointLegToDiagramLeg,
      Common.twoPointInteractionOrderLegEquiv, hleg]
  · simp [interactionVertexPositionRelabel, Common.orderedTwoPointLegToDiagramLeg,
      Common.twoPointInteractionOrderLegEquiv, hleg, interactionOrderChange]

/-- Reindexing the same arbitrary-set diagram by two different interaction orders differs only by
the corresponding explicit interaction-slot relabeling. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_changeOrder
    {S : Finset (Fin N)} (i j : Mode)
    (oldOrder newOrder : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    fixedExternalTwoPointWickDiagramOrderEquiv i j newOrder d =
      (fixedExternalTwoPointWickDiagramOrderEquiv i j oldOrder d).relabelInteractionVertices
        (interactionOrderChange oldOrder newOrder) := by
  apply Subtype.ext
  apply Common.TwoPointDiagram.ext
  · rfl
  · funext v
    change d.1.vertexLabel (newOrder v.1) =
      d.1.vertexLabel (oldOrder (interactionOrderChange oldOrder newOrder v.1))
    rw [interactionOrderChange_apply]
  · apply Pairing.ext
    funext p
    simp only [fixedExternalTwoPointWickDiagramOrderEquiv,
      Equiv.trans_apply, fixedExternalTwoPointWickDiagramOnEquivOrderedData,
      orderedFixedExternalTwoPointDataEquivFixedDiagram,
      FixedExternalTwoPointWickDiagram.relabelInteractionVertices_pairing,
      Pairing.relabel_partner]
    change _ = _
    rw [← Pairing.relabel_trans]
    rw [interactionVertexPositionRelabel_trans_orderedTwoPointLegToDiagramLeg]
    rfl

end Fermionic
end SecondQuantization
