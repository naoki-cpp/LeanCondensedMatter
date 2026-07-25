import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Reassemble

set_option linter.style.header false

/-!
# `reassemble (componentPartition d) F = d`: the "easy direction" of the mutual-inverse proof

Per review: unfolding `bigLegEquiv`/`sigmaProdDistrib`/`sigmaCongrRight`/`equivSigmaParts`/
`blockLegEquiv`/`subtypeMemBlockEquiv` all together at the point of use is unworkable. Instead this
file builds up a handful of small bridge facts that each avoid unfolding more than one or two of
these at a time:

- `QuarticWickDiagram.componentPartition_part`/`bigLegEquiv_legOfVertexLocal`: `componentPartition`
  and `bigLegEquiv` in terms of `componentBlock`/`Finpartition.equivSigmaParts` alone.
- `QuarticWickDiagram.bigLegEquiv_symm_sigma_mk`: the mirror (inverse-direction) fact.
- `QuarticWickDiagram.equivSigmaParts_symm_subtypeMemBlockEquiv`: any vertex of a genuine
  component block, routed through `subtypeMemBlockEquiv` and back through `equivSigmaParts`, is
  itself again — the core fact making both halves below work, for *any* vertex of the block (not
  just the one `equivSigmaParts` was built from), since a leg's pairing partner need not share its
  vertex.

These assemble into `QuarticWickDiagram.reassemble_componentPartition`: reassembling `d`'s own
`componentPartition` and `restrictComponentConnected` pieces reproduces `d` exactly. The converse
direction (`componentPartition (reassemble π F) = π` plus the dependent per-block family equality)
remains future work.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`d.componentPartition.part` agrees with `componentBlock`.** -/
theorem QuarticWickDiagram.componentPartition_part {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    d.componentPartition.part (v : Fin N) = d.componentBlock v :=
  d.componentPartition.part_eq_of_mem (d.componentBlock_mem_componentPartition v)
    (d.self_mem_componentBlock v)

/-- **`bigLegEquiv`'s value at a leg built from a vertex and local leg.** Once this is known,
`bigLegEquiv` itself never needs to be unfolded again. -/
theorem QuarticWickDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)} (π : Finpartition S)
    (v : ↥S) (i : Fin 4) :
    QuarticWickDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  have hqv : quarticLegEquiv S (legOfVertexLocal v i) = (v, i) :=
    Equiv.apply_symm_apply (quarticLegEquiv S) (v, i)
  simp only [QuarticWickDiagram.bigLegEquiv, Equiv.trans_apply, hqv, Equiv.prodCongr_apply,
    Equiv.sigmaProdDistrib_apply, Equiv.sigmaCongrRight_apply]
  rfl

/-- **`bigLegEquiv`'s inverse, applied to a leg built from a block and one of its own legs.**
The mirror image of `bigLegEquiv_legOfVertexLocal`. -/
theorem QuarticWickDiagram.bigLegEquiv_symm_sigma_mk {S : Finset (Fin N)} (π : Finpartition S)
    (B : π.parts) (leg' : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg'⟩ =
      legOfVertexLocal (π.equivSigmaParts.symm ⟨B, vertexOfLeg leg'⟩) (localLegOfLeg leg') := by
  have hqv : quarticLegEquiv (B : Finset (Fin N)) leg' = (vertexOfLeg leg', localLegOfLeg leg') :=
    rfl
  simp only [QuarticWickDiagram.bigLegEquiv, Equiv.symm_trans_apply, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply, Equiv.symm_symm, hqv, Equiv.sigmaProdDistrib_symm_apply,
    Equiv.prodCongr_symm, Equiv.refl_symm]
  rfl

/-- **`reassemble`'s vertex labels agree with `d`'s own**, when reassembling from `d`'s own
`componentPartition` and its `restrictComponentConnected` pieces. The "easy direction"'s
vertex-label half. -/
theorem QuarticWickDiagram.reassemble_componentPartition_vertexLabel {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    (QuarticWickDiagram.reassemble d.componentPartition
      fun B => d.restrictComponentConnected B.2).vertexLabel v = d.vertexLabel v := by
  set B := (d.componentPartition.equivSigmaParts v).1 with hBdef
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

/-- **The vertex `v` viewed back in its own `componentPartition` block, via
`subtypeMemBlockEquiv`'s inverse, is `v` itself.** The core fact underlying both the vertex-label
and pairing halves of `reassemble(componentPartition d) F = d`. -/
private theorem QuarticWickDiagram.subtypeMemBlockEquiv_symm_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    (((QuarticWickDiagram.subtypeMemBlockEquiv (d.componentPartition.equivSigmaParts v).1.1
        (d.componentPart_subset (d.componentPartition.equivSigmaParts v).1.2)).symm
        (d.componentPartition.equivSigmaParts v).2 :
        {w : ↥S // (w : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1}) : ↥S) = v :=
  Subtype.ext (by
    rw [QuarticWickDiagram.subtypeMemBlockEquiv_symm_val]
    simp [Finpartition.equivSigmaParts])

/-- **The forward direction of `subtypeMemBlockEquiv_symm_equivSigmaParts_snd`.** -/
private theorem QuarticWickDiagram.subtypeMemBlockEquiv_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (v : ↥S)
    (hv : (v : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1) :
    QuarticWickDiagram.subtypeMemBlockEquiv (d.componentPartition.equivSigmaParts v).1.1
      (d.componentPart_subset (d.componentPartition.equivSigmaParts v).1.2) ⟨v, hv⟩ =
      (d.componentPartition.equivSigmaParts v).2 := by
  rw [← Equiv.eq_symm_apply]
  exact (Subtype.ext (d.subtypeMemBlockEquiv_symm_equivSigmaParts_snd v)).symm

/-- **`subtypeMemBlockEquiv` preserves the underlying `Fin N` value, forwards.** The companion of
`subtypeMemBlockEquiv_symm_val`. -/
private theorem QuarticWickDiagram.subtypeMemBlockEquiv_val {S : Finset (Fin N)}
    {B : Finset (Fin N)} (hBS : B ⊆ S) (v : {v : ↥S // (v : Fin N) ∈ B}) :
    (QuarticWickDiagram.subtypeMemBlockEquiv B hBS v : Fin N) = (v : Fin N) := rfl

/-- **A vertex `w` of a genuine component block `B`, viewed through `subtypeMemBlockEquiv` then
back through `Finpartition.equivSigmaParts`, is `w` itself.** The general (any-vertex-in-`B`)
version of `subtypeMemBlockEquiv_symm_equivSigmaParts_snd`, needed for the pairing half since a
leg's partner need not be `v` itself. -/
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

/-- **`reassemble`'s pairing partner agrees with `d`'s own**, when reassembling from `d`'s own
`componentPartition` and its `restrictComponentConnected` pieces. The "easy direction"'s pairing
half. -/
theorem QuarticWickDiagram.reassemble_componentPartition_partner {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) (i : Fin 4) :
    (QuarticWickDiagram.reassemble d.componentPartition
        fun B => d.restrictComponentConnected B.2).pairing.partner (legOfVertexLocal v i) =
      d.pairing.partner (legOfVertexLocal v i) := by
  set B := (d.componentPartition.equivSigmaParts v).1 with hBdef
  set v' := (d.componentPartition.equivSigmaParts v).2 with hv'def
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
  set w := vertexOfLeg (d.pairing.partner (legOfVertexLocal v i)) with hwdef
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

/-- **`reassemble(d.componentPartition)(fun B => d.restrictComponentConnected B.2) = d`**: the
"easy direction" of the mutual-inverse equivalence, in full. -/
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
