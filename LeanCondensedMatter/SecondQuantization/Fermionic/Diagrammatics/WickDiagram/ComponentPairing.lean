import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairValue

set_option linter.style.header false

/-!
# Component-local ordered pairing compatibility

This module relates the pairing transported to an assembled global vertex order to the pairings
transported to each component-local order.  It first compares both ordered-leg enumerations through
the diagram's fixed flattened-leg coordinates, then proves that the component ordered-leg embedding
intertwines the corresponding partner permutations.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- Embed a flattened leg of a restricted component into the ambient diagram's fixed flattened-leg
enumeration. -/
noncomputable def QuarticWickDiagram.componentDiagramLeg {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => ((d.blockLegEquiv B.2).symm p).1

/-- Passing a component-local ordered leg to the ambient fixed diagram-leg coordinates agrees with
first embedding it into the assembled global ordered-leg enumeration. -/
theorem QuarticWickDiagram.orderedLegToDiagramLeg_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p) =
      d.componentDiagramLeg B
        (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p) := by
  apply (quarticLegEquiv S).injective
  simp [QuarticWickDiagram.componentDiagramLeg, orderedLegToDiagramLeg,
    QuarticWickDiagram.componentOrderedLeg, QuarticWickDiagram.assembleVertexOrder,
    Common.QuarticDiagram.assembleVertexOrder, Common.QuarticDiagram.componentVertexEquiv,
    Common.QuarticDiagram.blockLegEquiv, Common.QuarticDiagram.subtypeMemBlockEquiv,
    Finpartition.equivSigmaParts]

/-- The restricted pairing partner, transported back to ambient fixed diagram-leg coordinates,
agrees with the ambient diagram pairing partner. -/
theorem QuarticWickDiagram.componentDiagramLeg_restrictedPairing_partner
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentDiagramLeg B ((d.restrictedPairing B.2).partner p) =
      d.pairing.partner (d.componentDiagramLeg B p) := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.restrictedPairing_partner_blockLegEquiv B.2 leg
  have h' := congrArg
    (fun q => (((d.blockLegEquiv B.2).symm q :
      {leg : Fin (2 * (2 * S.card)) // d.legInBlock (B : Finset (Fin N)) leg}) :
        Fin (2 * (2 * S.card)))) h
  simpa [QuarticWickDiagram.componentDiagramLeg, leg] using h'

/-- The assembled global ordered pairing partner is the component ordered-leg embedding of the
component-local ordered pairing partner. -/
theorem QuarticWickDiagram.pairingInOrder_partner_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
        (d.componentOrderedLeg shuffle B p) =
      d.componentOrderedLeg shuffle B
        (((d.restrictComponent B.2).pairingInOrder (orders B)).partner p) := by
  apply (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)).injective
  simp only [QuarticWickDiagram.pairingInOrder, Common.QuarticDiagram.pairingInOrder,
    Common.BlochDeDominicis.Pairing.relabel_partner, Equiv.apply_symm_apply]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  simp only [QuarticWickDiagram.pairingInOrder, Common.QuarticDiagram.pairingInOrder,
    Common.BlochDeDominicis.Pairing.relabel_partner, Equiv.apply_symm_apply]
  rw [d.componentDiagramLeg_restrictedPairing_partner B]

end SecondQuantization
