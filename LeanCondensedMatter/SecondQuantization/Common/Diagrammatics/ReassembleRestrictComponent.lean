import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleComponentPartitionEq

set_option linter.style.header false

/-!
# Restricting a reassembled labelled quartic diagram

Restricting `QuarticDiagram.reassemble π F` to a block of `π` recovers that block's original
labelled quartic diagram.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

private theorem QuarticDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm
    {S : Finset (Fin N)} (π : Finpartition S) (B : π.parts)
    (v : ↥(B : Finset (Fin N))) :
    QuarticDiagram.reassembleVertex π B v =
      ((QuarticDiagram.subtypeMemBlockEquiv (B : Finset (Fin N)) (π.le B.2)).symm v : ↥S) := by
  apply Subtype.ext
  change (π.equivSigmaParts.symm ⟨B, v⟩ : Fin N) = _
  rw [QuarticDiagram.subtypeMemBlockEquiv_symm_val]
  rfl

private theorem QuarticDiagram.equivSigmaParts_subtypeMemBlockEquiv_symm
    {S : Finset (Fin N)} (π : Finpartition S) (B : π.parts)
    (v : ↥(B : Finset (Fin N))) :
    π.equivSigmaParts
        (((QuarticDiagram.subtypeMemBlockEquiv (B : Finset (Fin N)) (π.le B.2)).symm v : ↥S)) =
      ⟨B, v⟩ := by
  rw [← QuarticDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm]
  exact π.equivSigmaParts.apply_symm_apply ⟨B, v⟩

private theorem QuarticDiagram.restrictComponent_reassemble_vertexLabel
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts)
    (v : ↥(B : Finset (Fin N))) :
    ((QuarticDiagram.reassemble π F).restrictComponent hB').vertexLabel v =
      (F B).1.vertexLabel v := by
  set u := (((QuarticDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
    ((QuarticDiagram.reassemble π F).componentPart_subset hB')).symm v : ↥S)) with hu
  change (F (π.equivSigmaParts u).1).1.vertexLabel (π.equivSigmaParts u).2 =
      (F B).1.vertexLabel v
  have hueq : u = ((QuarticDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
      (π.le B.2)).symm v : ↥S) := hu
  rw [hueq, QuarticDiagram.equivSigmaParts_subtypeMemBlockEquiv_symm]

private theorem QuarticDiagram.blockLegEquiv_symm_reassemble_val {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts)
    (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((((QuarticDiagram.reassemble π F).blockLegEquiv hB').symm leg :
        {leg : Fin (2 * (2 * S.card)) //
          (QuarticDiagram.reassemble π F).legInBlock (B : Finset (Fin N)) leg}) :
        Fin (2 * (2 * S.card))) =
      (QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩ := by
  rw [QuarticDiagram.bigLegEquiv_symm_sigma_mk]
  change legOfVertexLocal
      ((((QuarticDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
        ((QuarticDiagram.reassemble π F).componentPart_subset hB')).symm
          (vertexOfLeg leg) : {v : ↥S // (v : Fin N) ∈ (B : Finset (Fin N))}) : ↥S))
      (localLegOfLeg leg) =
    legOfVertexLocal (QuarticDiagram.reassembleVertex π B (vertexOfLeg leg))
      (localLegOfLeg leg)
  apply congrArg (fun v : ↥S => legOfVertexLocal v (localLegOfLeg leg))
  simpa using
    (QuarticDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm π B
      (vertexOfLeg leg)).symm

private theorem QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts) (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticDiagram.reassemble π F).pairing.partner
        ((QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩) =
      (QuarticDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
  have hlhs : (QuarticDiagram.reassemble π F).pairing.partner =
      (QuarticDiagram.bigLegEquiv π).symm.permCongr
        (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

private theorem QuarticDiagram.restrictComponent_reassemble_pairing
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts) :
    ((QuarticDiagram.reassemble π F).restrictComponent hB').pairing = (F B).1.pairing := by
  change (QuarticDiagram.reassemble π F).restrictedPairing hB' = (F B).1.pairing
  apply Combinatorics.Pairing.ext
  apply Equiv.ext
  intro leg
  have hrestricted :=
    (QuarticDiagram.reassemble π F).restrictedPairing_partner_blockLegEquiv hB'
      (((QuarticDiagram.reassemble π F).blockLegEquiv hB').symm leg)
  rw [Equiv.apply_symm_apply] at hrestricted
  rw [hrestricted]
  apply ((QuarticDiagram.reassemble π F).blockLegEquiv hB').symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rw [(QuarticDiagram.reassemble π F).restrictedPartner_val B,
    QuarticDiagram.blockLegEquiv_symm_reassemble_val π F B hB' leg,
    QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk π F B leg,
    QuarticDiagram.blockLegEquiv_symm_reassemble_val π F B hB'
      ((F B).1.pairing.partner leg)]

/-- Restricting a reassembled diagram to one partition block recovers that block's diagram. -/
theorem QuarticDiagram.restrictComponent_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts) :
    (QuarticDiagram.reassemble π F).restrictComponent hB' = (F B).1 := by
  refine QuarticDiagram.ext
    (funext fun v =>
      QuarticDiagram.restrictComponent_reassemble_vertexLabel π F B hB' v) ?_
  exact QuarticDiagram.restrictComponent_reassemble_pairing π F B hB'

end Common
end SecondQuantization
