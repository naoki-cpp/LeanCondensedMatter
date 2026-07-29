import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairValue

set_option linter.style.header false

/-!
# Component-local ordered pairing compatibility

This module relates the pairing transported to an assembled global vertex order to the pairings
transported to each component-local order. It first compares both ordered-leg enumerations through
the diagram's fixed flattened-leg coordinates, then proves that the component ordered-leg embedding
intertwines the corresponding partner permutations.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

@[simp]
theorem vertexOfLeg_orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : QuarticVertexOrder S) (p : Fin (2 * (2 * S.card))) :
    vertexOfLeg (orderedLegToDiagramLeg S order p) =
      order (orderedQuarticLegEquiv S.card p).1 := by
  change ((quarticLegEquiv S) ((Common.orderedLegToDiagramLeg S order) p)).1 = _
  simp [Common.orderedLegToDiagramLeg]

@[simp]
theorem localLegOfLeg_orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : QuarticVertexOrder S) (p : Fin (2 * (2 * S.card))) :
    localLegOfLeg (orderedLegToDiagramLeg S order p) =
      (orderedQuarticLegEquiv S.card p).2 := by
  change ((quarticLegEquiv S) ((Common.orderedLegToDiagramLeg S order) p)).2 = _
  simp [Common.orderedLegToDiagramLeg]

/-- Recover the flattened ordered-leg value from its vertex slot and local leg. -/
theorem orderedQuarticLegEquiv_reconstruct_val (n : ℕ) (p : Fin (2 * (2 * n))) :
    p.val = (orderedQuarticLegEquiv n p).2.val + 4 * (orderedQuarticLegEquiv n p).1.val := by
  have h := congrArg (fun q => q.val) ((orderedQuarticLegEquiv n).symm_apply_apply p)
  simpa [orderedQuarticLegEquiv, finProdFinEquiv] using h.symm

/-- Embed a flattened leg of a restricted component into the ambient diagram's fixed flattened-leg
enumeration. -/
noncomputable def QuarticWickDiagram.componentDiagramLeg {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => ((d.blockLegEquiv B.2).symm p).1

/-- `componentDiagramLeg` preserves the underlying labelled vertex. -/
theorem QuarticWickDiagram.vertexOfLeg_componentDiagramLeg_val
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((vertexOfLeg (d.componentDiagramLeg B p) : ↥S) : Fin N) =
      ((vertexOfLeg p : ↥(B : Finset (Fin N))) : Fin N) := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.vertexOfLeg_blockLegEquiv B.2 leg
  have h' := congrArg (fun v : ↥(B : Finset (Fin N)) => (v : Fin N)) h
  simpa [QuarticWickDiagram.componentDiagramLeg, leg,
    Common.QuarticDiagram.subtypeMemBlockEquiv] using h'.symm

/-- `componentDiagramLeg` preserves the local leg index. -/
theorem QuarticWickDiagram.localLegOfLeg_componentDiagramLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    localLegOfLeg (d.componentDiagramLeg B p) = localLegOfLeg p := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.localLegOfLeg_blockLegEquiv B.2 leg
  simpa [QuarticWickDiagram.componentDiagramLeg, leg] using h.symm

/-- Numeric form of the component ordered-leg embedding. -/
@[simp]
theorem QuarticWickDiagram.componentOrderedLeg_val {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLeg shuffle B p).val =
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2.val +
        4 * (shuffle.slotEquiv
          ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩).val := by
  simp [QuarticWickDiagram.componentOrderedLeg, orderedQuarticLegEquiv, finProdFinEquiv]

/-- The component ordered-leg embedding preserves the flattened-leg order. -/
theorem QuarticWickDiagram.componentOrderedLeg_strictMono {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    StrictMono (d.componentOrderedLeg shuffle B) := by
  intro a b hab
  let pa := orderedQuarticLegEquiv (B : Finset (Fin N)).card a
  let pb := orderedQuarticLegEquiv (B : Finset (Fin N)).card b
  have ha := orderedQuarticLegEquiv_reconstruct_val (B : Finset (Fin N)).card a
  have hb := orderedQuarticLegEquiv_reconstruct_val (B : Finset (Fin N)).card b
  change a.val = pa.2.val + 4 * pa.1.val at ha
  change b.val = pb.2.val + 4 * pb.1.val at hb
  change a.val < b.val at hab
  have hpa : pa.2.val < 4 := pa.2.isLt
  have hpb : pb.2.val < 4 := pb.2.isLt
  change (d.componentOrderedLeg shuffle B a).val <
    (d.componentOrderedLeg shuffle B b).val
  simp only [d.componentOrderedLeg_val]
  change pa.2.val + 4 * (shuffle.slotEquiv ⟨B, pa.1⟩).val <
    pb.2.val + 4 * (shuffle.slotEquiv ⟨B, pb.1⟩).val
  by_cases hslot : pa.1 < pb.1
  · have hg : (shuffle.slotEquiv ⟨B, pa.1⟩).val <
        (shuffle.slotEquiv ⟨B, pb.1⟩).val := shuffle.strictMono B hslot
    omega
  · have hpb_le : pb.1 ≤ pa.1 := le_of_not_gt hslot
    have hs : pa.1 = pb.1 := by
      by_contra hne
      have hrev : pb.1 < pa.1 := lt_of_le_of_ne hpb_le (Ne.symm hne)
      have hrev_val : pb.1.val < pa.1.val := hrev
      omega
    have hs_val : pa.1.val = pb.1.val := congrArg (fun q => q.val) hs
    have hlocal : pa.2.val < pb.2.val := by omega
    have hg_eq : shuffle.slotEquiv ⟨B, pa.1⟩ =
        shuffle.slotEquiv ⟨B, pb.1⟩ := by rw [hs]
    have hg_val := congrArg (fun q => q.val) hg_eq
    omega

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
  apply Prod.ext
  · change vertexOfLeg
      (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p)) =
      vertexOfLeg
        (d.componentDiagramLeg B
          (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))
    apply Subtype.ext
    simp only [vertexOfLeg_orderedLegToDiagramLeg,
      d.orderedQuarticLegEquiv_componentOrderedLeg]
    calc
      ((d.assembleVertexOrder orders shuffle
          (shuffle.slotEquiv
            ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩) : ↥S) : Fin N) =
          ((orders B (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1 :
            ↥(B : Finset (Fin N))) : Fin N) :=
        d.assembleVertexOrder_componentSlot_val orders shuffle B _
      _ = ((vertexOfLeg
          (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p) :
            ↥(B : Finset (Fin N))) : Fin N) := by simp
      _ = ((vertexOfLeg
          (d.componentDiagramLeg B
            (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)) : ↥S) : Fin N) :=
        (d.vertexOfLeg_componentDiagramLeg_val B _).symm
  · change localLegOfLeg
      (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p)) =
      localLegOfLeg
        (d.componentDiagramLeg B
          (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))
    simp [d.localLegOfLeg_componentDiagramLeg]

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
  calc
    d.componentDiagramLeg B ((d.restrictedPairing B.2).partner p) =
        ((d.restrictedPartner B.2 leg :
          {leg : Fin (2 * (2 * S.card)) // d.legInBlock (B : Finset (Fin N)) leg}) :
            Fin (2 * (2 * S.card))) := by
      simpa [QuarticWickDiagram.componentDiagramLeg, leg] using h'
    _ = d.pairing.partner (d.componentDiagramLeg B p) := by
      rw [d.restrictedPartner_val B.2]
      rfl

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
  simp only [Common.QuarticDiagram.pairingInOrder,
    Common.BlochDeDominicis.Pairing.relabel_partner, Equiv.apply_symm_apply]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.restrictComponent_pairing B.2]
  simpa only [Equiv.apply_symm_apply] using
    (d.componentDiagramLeg_restrictedPairing_partner B
      (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)).symm

end SecondQuantization
