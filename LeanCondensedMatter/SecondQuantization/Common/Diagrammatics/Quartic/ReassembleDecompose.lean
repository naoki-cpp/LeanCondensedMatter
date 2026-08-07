import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ReassembleRestrictComponent

set_option linter.style.header false

/-!
# Reassembling a labelled quartic diagram from its connected components

Reassembling a labelled quartic diagram from its component partition and connected restrictions
recovers the original diagram.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

private theorem QuarticDiagram.reassemble_componentPartition_vertexLabel
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) :
    (QuarticDiagram.reassemble d.componentPartition
      fun B => d.restrictComponentConnected B.2).vertexLabel v = d.vertexLabel v := by
  set B := (d.componentPartition.equivSigmaParts v).1
  set v' := (d.componentPartition.equivSigmaParts v).2 with hv'def
  change (d.restrictComponent B.2).vertexLabel v' = d.vertexLabel v
  have hval : (((QuarticDiagram.subtypeMemBlockEquiv B.1
      (d.componentPart_subset B.2)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : Fin N) =
      (v : Fin N) := by
    rw [QuarticDiagram.subtypeMemBlockEquiv_symm_val, hv'def]
    simp [Finpartition.equivSigmaParts]
  have heq : (((QuarticDiagram.subtypeMemBlockEquiv B.1
      (d.componentPart_subset B.2)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : ↥S) = v :=
    Subtype.ext hval
  change d.vertexLabel (((QuarticDiagram.subtypeMemBlockEquiv B.1
      (d.componentPart_subset B.2)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : ↥S) =
      d.vertexLabel v
  rw [heq]

private theorem QuarticDiagram.subtypeMemBlockEquiv_symm_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) :
    (((QuarticDiagram.subtypeMemBlockEquiv (d.componentPartition.equivSigmaParts v).1.1
        (d.componentPart_subset (d.componentPartition.equivSigmaParts v).1.2)).symm
        (d.componentPartition.equivSigmaParts v).2 :
        {w : ↥S // (w : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1}) : ↥S) = v :=
  Subtype.ext (by
    rw [QuarticDiagram.subtypeMemBlockEquiv_symm_val]
    simp [Finpartition.equivSigmaParts])

private theorem QuarticDiagram.subtypeMemBlockEquiv_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S)
    (hv : (v : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1) :
    QuarticDiagram.subtypeMemBlockEquiv (d.componentPartition.equivSigmaParts v).1.1
      (d.componentPart_subset (d.componentPartition.equivSigmaParts v).1.2) ⟨v, hv⟩ =
      (d.componentPartition.equivSigmaParts v).2 := by
  rw [← Equiv.eq_symm_apply]
  exact (Subtype.ext (d.subtypeMemBlockEquiv_symm_equivSigmaParts_snd v)).symm

private theorem QuarticDiagram.subtypeMemBlockEquiv_val {S : Finset (Fin N)}
    {B : Finset (Fin N)} (hBS : B ⊆ S) (v : {v : ↥S // (v : Fin N) ∈ B}) :
    (QuarticDiagram.subtypeMemBlockEquiv B hBS v : Fin N) = (v : Fin N) := rfl

private theorem QuarticDiagram.equivSigmaParts_symm_subtypeMemBlockEquiv
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (w : ↥S) (hw : (w : Fin N) ∈ B) :
    d.componentPartition.equivSigmaParts.symm
      ⟨⟨B, hB⟩, QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨w, hw⟩⟩ =
      w := by
  apply Subtype.ext
  change (QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨w, hw⟩ : Fin N) =
    (w : Fin N)
  exact QuarticDiagram.subtypeMemBlockEquiv_val _ _

private theorem QuarticDiagram.reassemble_componentPartition_partner
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) (i : Fin 4) :
    (QuarticDiagram.reassemble d.componentPartition
        fun B => d.restrictComponentConnected B.2).pairing.partner (legOfVertexLocal v i) =
      d.pairing.partner (legOfVertexLocal v i) := by
  set B := (d.componentPartition.equivSigmaParts v).1
  set v' := (d.componentPartition.equivSigmaParts v).2
  have hv : (v : Fin N) ∈ B.1 := d.componentPartition.mem_part v.2
  have hleg0 : d.legInBlock B.1 (legOfVertexLocal v i) := by
    unfold QuarticDiagram.legInBlock
    rw [vertexOfLeg_legOfVertexLocal]
    exact (d.componentBlock_eq_iff_mem B.2 v).mpr hv
  have hv1 : vertexOfLeg (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩) = v' := by
    rw [QuarticDiagram.vertexOfLeg_blockLegEquiv]
    refine (congrArg (QuarticDiagram.subtypeMemBlockEquiv B.1 (d.componentPart_subset B.2))
      (Subtype.ext (a1 := (⟨vertexOfLeg (legOfVertexLocal v i), by
            simpa only [vertexOfLeg_legOfVertexLocal] using hv⟩ :
          {x : ↥S // (x : Fin N) ∈ B.1}))
        (a2 := (⟨v, hv⟩ : {x : ↥S // (x : Fin N) ∈ B.1}))
        (vertexOfLeg_legOfVertexLocal v i))).trans ?_
    exact d.subtypeMemBlockEquiv_equivSigmaParts_snd v hv
  have hl1 : localLegOfLeg (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩) = i := by
    rw [QuarticDiagram.localLegOfLeg_blockLegEquiv, localLegOfLeg_legOfVertexLocal]
  have hblock0 : d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩ = legOfVertexLocal v' i := by
    conv_lhs => rw [← QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg
      (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩)]
    rw [hv1, hl1]
  set w := vertexOfLeg (d.pairing.partner (legOfVertexLocal v i))
  have hw : (w : Fin N) ∈ B.1 := by
    have hpartner := (d.legInBlock_partner_iff (B := B.1) (legOfVertexLocal v i)).mp hleg0
    unfold QuarticDiagram.legInBlock at hpartner
    exact (d.componentBlock_eq_iff_mem B.2 _).mp hpartner
  have hv2 : vertexOfLeg
      (d.blockLegEquiv B.2 (d.restrictedPartner B.1 ⟨legOfVertexLocal v i, hleg0⟩)) =
      QuarticDiagram.subtypeMemBlockEquiv B.1 (d.componentPart_subset B.2) ⟨w, hw⟩ := by
    rw [QuarticDiagram.vertexOfLeg_blockLegEquiv]
    refine congrArg (QuarticDiagram.subtypeMemBlockEquiv B.1 (d.componentPart_subset B.2)) ?_
    apply Subtype.ext
    change (vertexOfLeg (d.restrictedPartner B.1 ⟨legOfVertexLocal v i, hleg0⟩ :
      Fin (2 * (2 * S.card))) : ↥S) = w
    rw [QuarticDiagram.restrictedPartner_val]
  have hl2 : localLegOfLeg
      (d.blockLegEquiv B.2 (d.restrictedPartner B.1 ⟨legOfVertexLocal v i, hleg0⟩)) =
      localLegOfLeg (d.pairing.partner (legOfVertexLocal v i)) := by
    rw [QuarticDiagram.localLegOfLeg_blockLegEquiv, QuarticDiagram.restrictedPartner_val]
  have hlhs :
      (QuarticDiagram.reassemble d.componentPartition
          fun B => d.restrictComponentConnected B.2).pairing.partner =
        (QuarticDiagram.bigLegEquiv d.componentPartition).symm.permCongr
          (Equiv.sigmaCongrRight
            fun B => (d.restrictComponentConnected B.2).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm,
    QuarticDiagram.bigLegEquiv_legOfVertexLocal, Equiv.sigmaCongrRight_apply,
    show (d.restrictComponentConnected B.2).1.pairing = d.restrictedPairing B.2 from
      d.restrictComponent_pairing B.2,
    ← hblock0, QuarticDiagram.restrictedPairing_partner_blockLegEquiv,
    QuarticDiagram.bigLegEquiv_symm_sigma_mk, hv2, hl2,
    d.equivSigmaParts_symm_subtypeMemBlockEquiv B.2 w hw,
    QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]

/-- Reassembling a diagram's connected component restrictions recovers the diagram. -/
theorem QuarticDiagram.reassemble_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    QuarticDiagram.reassemble d.componentPartition
      (fun B => d.restrictComponentConnected B.2) = d := by
  refine QuarticDiagram.ext (funext d.reassemble_componentPartition_vertexLabel) ?_
  apply Combinatorics.Pairing.ext
  apply Equiv.ext
  intro leg
  rw [← QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg]
  exact d.reassemble_componentPartition_partner (vertexOfLeg leg) (localLegOfLeg leg)

end Common
end SecondQuantization
