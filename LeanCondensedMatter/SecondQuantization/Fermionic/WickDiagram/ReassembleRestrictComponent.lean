import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleComponentPartitionEq

set_option linter.style.header false

/-!
# Restricting a reassembled diagram

Restricting `QuarticWickDiagram.reassemble π F` to a block of `π` recovers that block's original
quartic Wick diagram.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

private theorem QuarticWickDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm
    {S : Finset (Fin N)} (π : Finpartition S) (B : π.parts)
    (v : ↥(B : Finset (Fin N))) :
    QuarticWickDiagram.reassembleVertex π B v =
      ((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N)) (π.le B.2)).symm v : ↥S) := by
  apply Subtype.ext
  change (π.equivSigmaParts.symm ⟨B, v⟩ : Fin N) = _
  rw [QuarticWickDiagram.subtypeMemBlockEquiv_symm_val]
  rfl

private theorem QuarticWickDiagram.equivSigmaParts_subtypeMemBlockEquiv_symm
    {S : Finset (Fin N)} (π : Finpartition S) (B : π.parts)
    (v : ↥(B : Finset (Fin N))) :
    π.equivSigmaParts
        (((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N)) (π.le B.2)).symm v : ↥S)) =
      ⟨B, v⟩ := by
  rw [← QuarticWickDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm]
  exact π.equivSigmaParts.apply_symm_apply ⟨B, v⟩

private theorem QuarticWickDiagram.restrictComponent_reassemble_vertexLabel
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts)
    (v : ↥(B : Finset (Fin N))) :
    ((QuarticWickDiagram.reassemble π F).restrictComponent hB').vertexLabel v =
      (F B).1.vertexLabel v := by
  set u := (((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
    ((QuarticWickDiagram.reassemble π F).componentPart_subset hB')).symm v : ↥S)) with hu
  change (F (π.equivSigmaParts u).1).1.vertexLabel (π.equivSigmaParts u).2 =
      (F B).1.vertexLabel v
  have hueq : u = ((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
      (π.le B.2)).symm v : ↥S) := hu
  rw [hueq, QuarticWickDiagram.equivSigmaParts_subtypeMemBlockEquiv_symm]

private theorem QuarticWickDiagram.blockLegEquiv_symm_reassemble_val {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts)
    (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((((QuarticWickDiagram.reassemble π F).blockLegEquiv hB').symm leg :
        {leg : Fin (2 * (2 * S.card)) //
          (QuarticWickDiagram.reassemble π F).legInBlock (B : Finset (Fin N)) leg}) :
        Fin (2 * (2 * S.card))) =
      (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg⟩ := by
  rw [QuarticWickDiagram.bigLegEquiv_symm_sigma_mk]
  change legOfVertexLocal
      ((((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
        ((QuarticWickDiagram.reassemble π F).componentPart_subset hB')).symm
          (vertexOfLeg leg) : {v : ↥S // (v : Fin N) ∈ (B : Finset (Fin N))}) : ↥S))
      (localLegOfLeg leg) =
    legOfVertexLocal (QuarticWickDiagram.reassembleVertex π B (vertexOfLeg leg))
      (localLegOfLeg leg)
  apply congrArg (fun v : ↥S => legOfVertexLocal v (localLegOfLeg leg))
  simpa using
    (QuarticWickDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm π B
      (vertexOfLeg leg)).symm

private theorem QuarticWickDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts) (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticWickDiagram.reassemble π F).pairing.partner
        ((QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg⟩) =
      (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
  have hlhs : (QuarticWickDiagram.reassemble π F).pairing.partner =
      (QuarticWickDiagram.bigLegEquiv π).symm.permCongr
        (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

private theorem QuarticWickDiagram.restrictComponent_reassemble_pairing
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    ((QuarticWickDiagram.reassemble π F).restrictComponent hB').pairing = (F B).1.pairing := by
  change (QuarticWickDiagram.reassemble π F).restrictedPairing hB' = (F B).1.pairing
  apply Common.BlochDeDominicis.Pairing.ext
  apply Equiv.ext
  intro leg
  have hrestricted :=
    (QuarticWickDiagram.reassemble π F).restrictedPairing_partner_blockLegEquiv hB'
      (((QuarticWickDiagram.reassemble π F).blockLegEquiv hB').symm leg)
  rw [Equiv.apply_symm_apply] at hrestricted
  rw [hrestricted]
  apply ((QuarticWickDiagram.reassemble π F).blockLegEquiv hB').symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rw [(QuarticWickDiagram.reassemble π F).restrictedPartner_val,
    QuarticWickDiagram.blockLegEquiv_symm_reassemble_val π F B hB' leg,
    QuarticWickDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk π F B leg,
    QuarticWickDiagram.blockLegEquiv_symm_reassemble_val π F B hB'
      ((F B).1.pairing.partner leg)]

/-- Restricting a reassembled diagram to one partition block recovers that block's diagram. -/
theorem QuarticWickDiagram.restrictComponent_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    (QuarticWickDiagram.reassemble π F).restrictComponent hB' = (F B).1 := by
  refine QuarticWickDiagram.ext
    (funext fun v =>
      QuarticWickDiagram.restrictComponent_reassemble_vertexLabel π F B hB' v) ?_
  exact QuarticWickDiagram.restrictComponent_reassemble_pairing π F B hB'

end SecondQuantization
