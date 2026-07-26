import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Reassemble

set_option linter.style.header false

/-!
# Reassembling a diagram from its connected components

Reassembling a quartic Wick diagram from its component partition and connected restrictions recovers
the original diagram.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

private theorem QuarticWickDiagram.reassemble_componentPartition_vertexLabel
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    (QuarticWickDiagram.reassemble d.componentPartition
      fun B => d.restrictComponentConnected B.2).vertexLabel v = d.vertexLabel v := by
  set B := (d.componentPartition.equivSigmaParts v).1
  set v' := (d.componentPartition.equivSigmaParts v).2 with hv'def
  change (d.restrictComponent B.2).vertexLabel v' = d.vertexLabel v
  have hval : (((QuarticWickDiagram.subtypeMemBlockEquiv B.1
      (d.componentPart_subset B.2)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : Fin N) =
      (v : Fin N) := by
    rw [QuarticWickDiagram.subtypeMemBlockEquiv_symm_val, hv'def]
    simp [Finpartition.equivSigmaParts]
  have heq : (((QuarticWickDiagram.subtypeMemBlockEquiv B.1
      (d.componentPart_subset B.2)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : ↥S) = v :=
    Subtype.ext hval
  change d.vertexLabel (((QuarticWickDiagram.subtypeMemBlockEquiv B.1
      (d.componentPart_subset B.2)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : ↥S) =
      d.vertexLabel v
  rw [heq]

private theorem QuarticWickDiagram.subtypeMemBlockEquiv_symm_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    (((QuarticWickDiagram.subtypeMemBlockEquiv (d.componentPartition.equivSigmaParts v).1.1
        (d.componentPart_subset (d.componentPartition.equivSigmaParts v).1.2)).symm
        (d.componentPartition.equivSigmaParts v).2 :
        {w : ↥S // (w : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1}) : ↥S) = v :=
  Subtype.ext (by
    rw [QuarticWickDiagram.subtypeMemBlockEquiv_symm_val]
    simp [Finpartition.equivSigmaParts])

private theorem QuarticWickDiagram.subtypeMemBlockEquiv_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (v : ↥S)
    (hv : (v : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1) :
    QuarticWickDiagram.subtypeMemBlockEquiv (d.componentPartition.equivSigmaParts v).1.1
      (d.componentPart_subset (d.componentPartition.equivSigmaParts v).1.2) ⟨v, hv⟩ =
      (d.componentPartition.equivSigmaParts v).2 := by
  rw [← Equiv.eq_symm_apply]
  exact (Subtype.ext (d.subtypeMemBlockEquiv_symm_equivSigmaParts_snd v)).symm

private theorem QuarticWickDiagram.subtypeMemBlockEquiv_val {S : Finset (Fin N)}
    {B : Finset (Fin N)} (hBS : B ⊆ S) (v : {v : ↥S // (v : Fin N) ∈ B}) :
    (QuarticWickDiagram.subtypeMemBlockEquiv B hBS v : Fin N) = (v : Fin N) := rfl

private theorem QuarticWickDiagram.equivSigmaParts_symm_subtypeMemBlockEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (w : ↥S) (hw : (w : Fin N) ∈ B) :
    d.componentPartition.equivSigmaParts.symm
      ⟨⟨B, hB⟩, QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨w, hw⟩⟩ =
      w := by
  apply Subtype.ext
  change (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨w, hw⟩ : Fin N) =
    (w : Fin N)
  exact QuarticWickDiagram.subtypeMemBlockEquiv_val _ _

private theorem QuarticWickDiagram.reassemble_componentPartition_partner
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (v : ↥S) (i : Fin 4) :
    (QuarticWickDiagram.reassemble d.componentPartition
        fun B => d.restrictComponentConnected B.2).pairing.partner (legOfVertexLocal v i) =
      d.pairing.partner (legOfVertexLocal v i) := by
  set B := (d.componentPartition.equivSigmaParts v).1
  set v' := (d.componentPartition.equivSigmaParts v).2
  have hv : (v : Fin N) ∈ B.1 := d.componentPartition.mem_part v.2
  have hleg0 : d.legInBlock B.1 (legOfVertexLocal v i) := by
    unfold QuarticWickDiagram.legInBlock
    rw [vertexOfLeg_legOfVertexLocal]
    exact hv
  have hv1 : vertexOfLeg (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩) = v' := by
    rw [QuarticWickDiagram.vertexOfLeg_blockLegEquiv]
    refine (congrArg (QuarticWickDiagram.subtypeMemBlockEquiv B.1 (d.componentPart_subset B.2))
      (Subtype.ext (a1 := (⟨vertexOfLeg (legOfVertexLocal v i), hleg0⟩ :
          {x : ↥S // (x : Fin N) ∈ B.1}))
        (a2 := (⟨v, hv⟩ : {x : ↥S // (x : Fin N) ∈ B.1}))
        (vertexOfLeg_legOfVertexLocal v i))).trans ?_
    exact d.subtypeMemBlockEquiv_equivSigmaParts_snd v hv
  have hl1 : localLegOfLeg (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩) = i := by
    rw [QuarticWickDiagram.localLegOfLeg_blockLegEquiv, localLegOfLeg_legOfVertexLocal]
  have hblock0 : d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩ = legOfVertexLocal v' i := by
    conv_lhs => rw [← QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg
      (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩)]
    rw [hv1, hl1]
  set w := vertexOfLeg (d.pairing.partner (legOfVertexLocal v i))
  have hw : (w : Fin N) ∈ B.1 := by
    have hpartner := (d.legInBlock_partner_iff B.2 (legOfVertexLocal v i)).mp hleg0
    unfold QuarticWickDiagram.legInBlock at hpartner
    exact hpartner
  have hv2 : vertexOfLeg
      (d.blockLegEquiv B.2 (d.restrictedPartner B.2 ⟨legOfVertexLocal v i, hleg0⟩)) =
      QuarticWickDiagram.subtypeMemBlockEquiv B.1 (d.componentPart_subset B.2) ⟨w, hw⟩ := by
    rw [QuarticWickDiagram.vertexOfLeg_blockLegEquiv]
    refine congrArg (QuarticWickDiagram.subtypeMemBlockEquiv B.1 (d.componentPart_subset B.2)) ?_
    apply Subtype.ext
    change (vertexOfLeg (d.restrictedPartner B.2 ⟨legOfVertexLocal v i, hleg0⟩ :
      Fin (2 * (2 * S.card))) : ↥S) = w
    rw [QuarticWickDiagram.restrictedPartner_val]
  have hl2 : localLegOfLeg
      (d.blockLegEquiv B.2 (d.restrictedPartner B.2 ⟨legOfVertexLocal v i, hleg0⟩)) =
      localLegOfLeg (d.pairing.partner (legOfVertexLocal v i)) := by
    rw [QuarticWickDiagram.localLegOfLeg_blockLegEquiv, QuarticWickDiagram.restrictedPartner_val]
  have hlhs :
      (QuarticWickDiagram.reassemble d.componentPartition
          fun B => d.restrictComponentConnected B.2).pairing.partner =
        (QuarticWickDiagram.bigLegEquiv d.componentPartition).symm.permCongr
          (Equiv.sigmaCongrRight
            fun B => (d.restrictComponentConnected B.2).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm,
    QuarticWickDiagram.bigLegEquiv_legOfVertexLocal, Equiv.sigmaCongrRight_apply,
    show (d.restrictComponentConnected B.2).1.pairing = d.restrictedPairing B.2 from
      d.restrictComponent_pairing B.2,
    ← hblock0, QuarticWickDiagram.restrictedPairing_partner_blockLegEquiv,
    QuarticWickDiagram.bigLegEquiv_symm_sigma_mk, hv2, hl2,
    d.equivSigmaParts_symm_subtypeMemBlockEquiv B.2 w hw,
    QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]

/-- Reassembling a diagram's connected component restrictions recovers the diagram. -/
theorem QuarticWickDiagram.reassemble_componentPartition {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :
    QuarticWickDiagram.reassemble d.componentPartition
      (fun B => d.restrictComponentConnected B.2) = d := by
  refine QuarticWickDiagram.ext (funext d.reassemble_componentPartition_vertexLabel) ?_
  apply Common.BlochDeDominicis.Pairing.ext
  apply Equiv.ext
  intro leg
  rw [← QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg]
  exact d.reassemble_componentPartition_partner (vertexOfLeg leg) (localLegOfLeg leg)

end SecondQuantization
