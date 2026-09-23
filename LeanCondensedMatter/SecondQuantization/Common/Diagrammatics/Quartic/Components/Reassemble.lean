import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected

set_option linter.style.header false

/-!
# Reassembling a labelled quartic diagram from connected pieces

Given a partition of the ambient vertex set and a connected labelled quartic diagram on each part,
this module glues the block diagrams into one diagram and proves the corresponding inverse laws:
reassembly preserves the chosen component partition, restriction recovers each connected block, and
reassembling a diagram's own connected-component decomposition recovers the original diagram. The
construction depends only on quartic leg indexing and pairings, not on the label type or particle
statistics.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- The ambient flattened legs, identified with the disjoint union of each partition part's legs. -/
noncomputable def QuarticDiagram.bigLegEquiv {S : Finset (Fin N)} (π : Finpartition S) :
    Fin (2 * (2 * S.card)) ≃ Σ B : π.parts, Fin (2 * (2 * (B : Finset (Fin N)).card)) :=
  (quarticLegEquiv S).trans <|
    (π.equivSigmaParts.prodCongr (Equiv.refl (Fin 4))).trans <|
      (Equiv.sigmaProdDistrib _ _).trans
        (Equiv.sigmaCongrRight fun B => (quarticLegEquiv (B : Finset (Fin N))).symm)

/-- `bigLegEquiv` at a leg constructed from an ambient vertex and a local leg. -/
theorem QuarticDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)}
    (π : Finpartition S) (v : ↥S) (i : Fin 4) :
    QuarticDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  have hqv : quarticLegEquiv S (legOfVertexLocal v i) = (v, i) :=
    Equiv.apply_symm_apply (quarticLegEquiv S) (v, i)
  simp only [QuarticDiagram.bigLegEquiv, Equiv.trans_apply, hqv, Equiv.prodCongr_apply,
    Equiv.sigmaProdDistrib_apply, Equiv.sigmaCongrRight_apply]
  rfl

/-- The inverse of `bigLegEquiv` at a leg belonging to one partition part. -/
theorem QuarticDiagram.bigLegEquiv_symm_sigma_mk {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts)
    (leg' : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticDiagram.bigLegEquiv π).symm ⟨B, leg'⟩ =
      legOfVertexLocal (π.equivSigmaParts.symm ⟨B, vertexOfLeg leg'⟩) (localLegOfLeg leg') := by
  have hqv : quarticLegEquiv (B : Finset (Fin N)) leg' =
      (vertexOfLeg leg', localLegOfLeg leg') := rfl
  simp only [QuarticDiagram.bigLegEquiv, Equiv.symm_trans_apply,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.symm_symm, hqv,
    Equiv.sigmaProdDistrib_symm_apply, Equiv.prodCongr_symm, Equiv.refl_symm]
  rfl

/-- The pairing on the ambient legs obtained by gluing the pairings of all partition parts. -/
noncomputable def QuarticDiagram.reassemblePairing {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    Combinatorics.Pairing (2 * S.card) :=
  (Combinatorics.PairingOn.sigmaCongrRight fun B => (F B).1.pairing).transport
    (QuarticDiagram.bigLegEquiv π)

/-- Reassemble an ambient labelled quartic diagram from connected diagrams on partition parts. -/
noncomputable def QuarticDiagram.reassemble {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    QuarticDiagram Label N S where
  vertexLabel v := (F (π.equivSigmaParts v).1).1.vertexLabel (π.equivSigmaParts v).2
  pairing := QuarticDiagram.reassemblePairing π F


/-- A vertex of a block `B`, included back into the ambient vertex set. -/
noncomputable def QuarticDiagram.reassembleVertex {S : Finset (Fin N)} (π : Finpartition S)
    (B : π.parts) (v : ↥(B : Finset (Fin N))) : ↥S :=
  π.equivSigmaParts.symm ⟨B, v⟩

private theorem QuarticDiagram.reassembleVertex_injective {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts) :
    Function.Injective (QuarticDiagram.reassembleVertex π B) := by
  intro v w hvw
  have h : (⟨B, v⟩ : Σ t : π.parts, ↥(t : Finset (Fin N))) = ⟨B, w⟩ :=
    π.equivSigmaParts.symm.injective hvw
  simpa using h

private theorem QuarticDiagram.bigLegEquiv_fst_eq_part {S : Finset (Fin N)}
    (π : Finpartition S) (leg : Fin (2 * (2 * S.card))) :
    ((QuarticDiagram.bigLegEquiv π leg).1 : Finset (Fin N)) =
      π.part (vertexOfLeg leg : Fin N) := by
  conv_lhs => rw [← QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg]
  rw [QuarticDiagram.bigLegEquiv_legOfVertexLocal]
  rfl

private theorem QuarticDiagram.reassemble_partner_bigLegEquiv_fst {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (leg : Fin (2 * (2 * S.card))) :
    (QuarticDiagram.bigLegEquiv π
        ((QuarticDiagram.reassemble π F).pairing.partner leg)).1 =
      (QuarticDiagram.bigLegEquiv π leg).1 := by
  have hlhs : (QuarticDiagram.reassemble π F).pairing.partner =
      (QuarticDiagram.bigLegEquiv π).symm.permCongr
        (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

private theorem QuarticDiagram.reassemble_vertexGraph_adj_same_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    {u w : ↥S} (h : (QuarticDiagram.reassemble π F).vertexGraph.Adj u w) :
    π.part (u : Fin N) = π.part (w : Fin N) := by
  obtain ⟨-, leg, hu, hw⟩ := h
  rw [← hu, ← hw, ← QuarticDiagram.bigLegEquiv_fst_eq_part,
    ← QuarticDiagram.bigLegEquiv_fst_eq_part,
    QuarticDiagram.reassemble_partner_bigLegEquiv_fst]

private theorem QuarticDiagram.reassemble_reachable_same_part {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    {u w : ↥S} (h : (QuarticDiagram.reassemble π F).vertexGraph.Reachable u w) :
    π.part (u : Fin N) = π.part (w : Fin N) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih =>
    exact (QuarticDiagram.reassemble_vertexGraph_adj_same_part π F hadj).trans ih

private theorem QuarticDiagram.reassemble_componentBlock_subset_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (v : ↥S) :
    (QuarticDiagram.reassemble π F).componentBlock v ⊆ π.part (v : Fin N) := by
  intro x hx
  change x ∈ (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn v at hx
  obtain ⟨hxS, hreach⟩ :=
    ((QuarticDiagram.reassemble π F).vertexGraph.mem_componentBlockOn v).1 hx
  rw [← QuarticDiagram.reassemble_reachable_same_part π F hreach]
  exact π.mem_part hxS

private theorem QuarticDiagram.reassemble_adj_of_adj_component {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts) {u' w' : ↥(B : Finset (Fin N))} (h : (F B).1.vertexGraph.Adj u' w') :
    (QuarticDiagram.reassemble π F).vertexGraph.Adj
      (QuarticDiagram.reassembleVertex π B u')
      (QuarticDiagram.reassembleVertex π B w') := by
  obtain ⟨hne', leg, hu', hw'⟩ := h
  set leg0 := (QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩ with hlegdef
  have hbig : QuarticDiagram.bigLegEquiv π leg0 = ⟨B, leg⟩ :=
    Equiv.apply_symm_apply _ _
  have hu : vertexOfLeg leg0 = QuarticDiagram.reassembleVertex π B u' := by
    rw [hlegdef, QuarticDiagram.bigLegEquiv_symm_sigma_mk]
    rw [vertexOfLeg_legOfVertexLocal, hu']
    rfl
  have hpartner :
      (QuarticDiagram.reassemble π F).pairing.partner leg0 =
        (QuarticDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
    have hlhs : (QuarticDiagram.reassemble π F).pairing.partner =
        (QuarticDiagram.bigLegEquiv π).symm.permCongr
          (Equiv.sigmaCongrRight fun C => (F C).1.pairing.partner) := rfl
    rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, hbig]
    rfl
  have hw : vertexOfLeg ((QuarticDiagram.reassemble π F).pairing.partner leg0) =
      QuarticDiagram.reassembleVertex π B w' := by
    rw [hpartner, QuarticDiagram.bigLegEquiv_symm_sigma_mk]
    rw [vertexOfLeg_legOfVertexLocal, hw']
    rfl
  exact ⟨fun hEq => hne' (QuarticDiagram.reassembleVertex_injective π B hEq),
    leg0, hu, hw⟩

private theorem QuarticDiagram.reassemble_reachable_of_reachable_component
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts) {u' w' : ↥(B : Finset (Fin N))}
    (h : (F B).1.vertexGraph.Reachable u' w') :
    (QuarticDiagram.reassemble π F).vertexGraph.Reachable
      (QuarticDiagram.reassembleVertex π B u')
      (QuarticDiagram.reassembleVertex π B w') := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    exact (SimpleGraph.Adj.reachable
      (QuarticDiagram.reassemble_adj_of_adj_component π F B hadj)).trans ih

private theorem QuarticDiagram.part_subset_reassemble_componentBlock
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (v : ↥S) :
    π.part (v : Fin N) ⊆ (QuarticDiagram.reassemble π F).componentBlock v := by
  intro x hx
  set B := (π.equivSigmaParts v).1
  have hxB : x ∈ (B : Finset (Fin N)) := hx
  have hxS : x ∈ S := π.le B.2 hxB
  have hreach0 : (F B).1.vertexGraph.Reachable (⟨x, hxB⟩ : ↥(B : Finset (Fin N)))
      (π.equivSigmaParts v).2 :=
    (F B).2.1 ⟨x, hxB⟩ (π.equivSigmaParts v).2
  have hreach := QuarticDiagram.reassemble_reachable_of_reachable_component π F B hreach0
  have heq1 : QuarticDiagram.reassembleVertex π B ⟨x, hxB⟩ = (⟨x, hxS⟩ : ↥S) := rfl
  have heq2 : QuarticDiagram.reassembleVertex π B (π.equivSigmaParts v).2 = v := by
    change π.equivSigmaParts.symm ⟨B, (π.equivSigmaParts v).2⟩ = v
    exact π.equivSigmaParts.symm_apply_apply v
  rw [heq1, heq2] at hreach
  change x ∈ (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn v
  exact ((QuarticDiagram.reassemble π F).vertexGraph.mem_componentBlockOn v).2
    ⟨hxS, hreach⟩

private theorem QuarticDiagram.reassemble_componentBlock_eq_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (v : ↥S) :
    (QuarticDiagram.reassemble π F).componentBlock v = π.part (v : Fin N) :=
  Finset.Subset.antisymm (QuarticDiagram.reassemble_componentBlock_subset_part π F v)
    (QuarticDiagram.part_subset_reassemble_componentBlock π F v)

/-- The component partition of a reassembled family is the original partition. -/
theorem QuarticDiagram.componentPartition_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    (QuarticDiagram.reassemble π F).componentPartition = π := by
  apply Finpartition.ext
  apply Finset.Subset.antisymm
  · intro B hB
    obtain ⟨v, hvS, hv⟩ :=
      (QuarticDiagram.reassemble π F).componentPartition.part_surjOn hB
    have hblock :
        (QuarticDiagram.reassemble π F).componentBlock (⟨v, hvS⟩ : ↥S) = B := by
      simpa only [QuarticDiagram.componentBlock] using hv
    rw [← hblock, QuarticDiagram.reassemble_componentBlock_eq_part]
    exact π.part_mem.2 hvS
  · intro B hB
    obtain ⟨v, hvS, hv⟩ := π.part_surjOn hB
    have hmem :
        (QuarticDiagram.reassemble π F).componentBlock (⟨v, hvS⟩ : ↥S) ∈
          (QuarticDiagram.reassemble π F).componentPartition.parts := by
      unfold QuarticDiagram.componentBlock
      exact (QuarticDiagram.reassemble π F).componentPartition.part_mem.2 hvS
    rwa [QuarticDiagram.reassemble_componentBlock_eq_part, hv] at hmem

private theorem QuarticDiagram.reassembleVertex_eq_subtypeSubtypeEquivSubtype_symm
    {S : Finset (Fin N)} (π : Finpartition S) (B : π.parts)
    (v : ↥(B : Finset (Fin N))) :
    QuarticDiagram.reassembleVertex π B v =
      ((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
        (q := (· ∈ (B : Finset (Fin N)))) (fun {_} hx => π.le B.2 hx)).symm v : ↥S) := by
  apply Subtype.ext
  change (π.equivSigmaParts.symm ⟨B, v⟩ : Fin N) = _
  rfl

private theorem QuarticDiagram.equivSigmaParts_subtypeSubtypeEquivSubtype_symm
    {S : Finset (Fin N)} (π : Finpartition S) (B : π.parts)
    (v : ↥(B : Finset (Fin N))) :
    π.equivSigmaParts
        (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
        (q := (· ∈ (B : Finset (Fin N)))) (fun {_} hx => π.le B.2 hx)).symm v : ↥S)) =
      ⟨B, v⟩ := by
  rw [← QuarticDiagram.reassembleVertex_eq_subtypeSubtypeEquivSubtype_symm]
  exact π.equivSigmaParts.apply_symm_apply ⟨B, v⟩

private theorem QuarticDiagram.restrictComponent_reassemble_vertexLabel
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts)
    (v : ↥(B : Finset (Fin N))) :
    ((QuarticDiagram.reassemble π F).restrictComponent hB').vertexLabel v =
      (F B).1.vertexLabel v := by
  set u := (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
    (q := (· ∈ (B : Finset (Fin N))))
    (fun {_} hx => (QuarticDiagram.reassemble π F).componentPartition.le hB' hx)).symm v : ↥S)) with hu
  change (F (π.equivSigmaParts u).1).1.vertexLabel (π.equivSigmaParts u).2 =
      (F B).1.vertexLabel v
  have hueq : u = ((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
        (q := (· ∈ (B : Finset (Fin N)))) (fun {_} hx => π.le B.2 hx)).symm v : ↥S) := hu
  rw [hueq, QuarticDiagram.equivSigmaParts_subtypeSubtypeEquivSubtype_symm]

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
      ((((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
        (q := (· ∈ (B : Finset (Fin N))))
        (fun {_} hx => (QuarticDiagram.reassemble π F).componentPartition.le hB' hx)).symm
          (vertexOfLeg leg) : {v : ↥S // (v : Fin N) ∈ (B : Finset (Fin N))}) : ↥S))
      (localLegOfLeg leg) =
    legOfVertexLocal (QuarticDiagram.reassembleVertex π B (vertexOfLeg leg))
      (localLegOfLeg leg)
  apply congrArg (fun v : ↥S => legOfVertexLocal v (localLegOfLeg leg))
  simpa using
    (QuarticDiagram.reassembleVertex_eq_subtypeSubtypeEquivSubtype_symm π B
      (vertexOfLeg leg)).symm

private theorem QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts) (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticDiagram.reassemble π F).pairing.partner
        ((QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩) =
      (QuarticDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
  simp [QuarticDiagram.reassemble, QuarticDiagram.reassemblePairing]

private theorem QuarticDiagram.restrictComponent_reassemble_pairing
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts) :
    ((QuarticDiagram.reassemble π F).restrictComponent hB').pairing = (F B).1.pairing := by
  change (QuarticDiagram.reassemble π F).restrictedPairing hB' = (F B).1.pairing
  apply Combinatorics.PairingOn.ext
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

private theorem QuarticDiagram.reassemble_componentPartition_vertexLabel
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) :
    (QuarticDiagram.reassemble d.componentPartition
      fun B => d.restrictComponentConnected B.2).vertexLabel v = d.vertexLabel v := by
  set B := (d.componentPartition.equivSigmaParts v).1
  set v' := (d.componentPartition.equivSigmaParts v).2 with hv'def
  change (d.restrictComponent B.2).vertexLabel v' = d.vertexLabel v
  have hval : (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B.1))
      (fun {_} hx => d.componentPartition.le B.2 hx)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : Fin N) =
      (v : Fin N) := by
    change (v' : Fin N) = (v : Fin N)
    rw [hv'def]
    simp [Finpartition.equivSigmaParts]
  have heq : (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B.1))
      (fun {_} hx => d.componentPartition.le B.2 hx)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : ↥S) = v :=
    Subtype.ext hval
  change d.vertexLabel (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B.1))
      (fun {_} hx => d.componentPartition.le B.2 hx)).symm v' : {v : ↥S // (v : Fin N) ∈ B.1}) : ↥S) =
      d.vertexLabel v
  rw [heq]

private theorem QuarticDiagram.subtypeSubtypeEquivSubtype_symm_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) :
    (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
        (q := (· ∈ (d.componentPartition.equivSigmaParts v).1.1))
        (fun {_} hx => d.componentPartition.le (d.componentPartition.equivSigmaParts v).1.2 hx)).symm
        (d.componentPartition.equivSigmaParts v).2 :
        {w : ↥S // (w : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1}) : ↥S) = v :=
  Subtype.ext (by
    change ((d.componentPartition.equivSigmaParts v).2 : Fin N) = (v : Fin N)
    simp [Finpartition.equivSigmaParts])

private theorem QuarticDiagram.subtypeSubtypeEquivSubtype_equivSigmaParts_snd
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S)
    (hv : (v : Fin N) ∈ (d.componentPartition.equivSigmaParts v).1.1) :
    Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
      (q := (· ∈ (d.componentPartition.equivSigmaParts v).1.1))
      (fun {_} hx => d.componentPartition.le (d.componentPartition.equivSigmaParts v).1.2 hx) ⟨v, hv⟩ =
      (d.componentPartition.equivSigmaParts v).2 := by
  rw [← Equiv.eq_symm_apply]
  exact (Subtype.ext (d.subtypeSubtypeEquivSubtype_symm_equivSigmaParts_snd v)).symm

private theorem QuarticDiagram.equivSigmaParts_symm_subtypeSubtypeEquivSubtype
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (w : ↥S) (hw : (w : Fin N) ∈ B) :
    d.componentPartition.equivSigmaParts.symm
      ⟨⟨B, hB⟩, Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B))
      (fun {_} hx => d.componentPartition.le hB hx) ⟨w, hw⟩⟩ =
      w := by
  apply Subtype.ext
  change (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B))
      (fun {_} hx => d.componentPartition.le hB hx) ⟨w, hw⟩ : Fin N) =
    (w : Fin N)
  rfl

private theorem QuarticDiagram.reassemble_componentPartition_partner
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) (i : Fin 4) :
    (QuarticDiagram.reassemble d.componentPartition
        fun B => d.restrictComponentConnected B.2).pairing.partner (legOfVertexLocal v i) =
      d.pairing.partner (legOfVertexLocal v i) := by
  set B := (d.componentPartition.equivSigmaParts v).1
  set v' := (d.componentPartition.equivSigmaParts v).2
  have hv : (v : Fin N) ∈ B.1 := d.componentPartition.mem_part v.2
  have hleg0 : d.legInBlock B.1 (legOfVertexLocal v i) := by
    unfold QuarticDiagram.legInBlock QuarticDiagram.componentBlock
    rw [vertexOfLeg_legOfVertexLocal]
    exact (d.componentPartition.part_eq_iff_mem B.2).mpr hv
  have hv1 : vertexOfLeg (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩) = v' := by
    rw [QuarticDiagram.vertexOfLeg_blockLegEquiv]
    refine (congrArg (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B.1))
      (fun {_} hx => d.componentPartition.le B.2 hx))
      (Subtype.ext (a1 := (⟨vertexOfLeg (legOfVertexLocal v i), by
            simpa only [vertexOfLeg_legOfVertexLocal] using hv⟩ :
          {x : ↥S // (x : Fin N) ∈ B.1}))
        (a2 := (⟨v, hv⟩ : {x : ↥S // (x : Fin N) ∈ B.1}))
        (vertexOfLeg_legOfVertexLocal v i))).trans ?_
    exact d.subtypeSubtypeEquivSubtype_equivSigmaParts_snd v hv
  have hl1 : localLegOfLeg (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩) = i := by
    rw [QuarticDiagram.localLegOfLeg_blockLegEquiv, localLegOfLeg_legOfVertexLocal]
  have hblock0 : d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩ = legOfVertexLocal v' i := by
    conv_lhs => rw [← QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg
      (d.blockLegEquiv B.2 ⟨legOfVertexLocal v i, hleg0⟩)]
    rw [hv1, hl1]
  set w := vertexOfLeg (d.pairing.partner (legOfVertexLocal v i))
  have hw : (w : Fin N) ∈ B.1 := by
    have hpartner := (d.legInBlock_partner_iff (B := B.1) (legOfVertexLocal v i)).mp hleg0
    unfold QuarticDiagram.legInBlock QuarticDiagram.componentBlock at hpartner
    exact (d.componentPartition.part_eq_iff_mem B.2).mp hpartner
  have hv2 : vertexOfLeg
      (d.blockLegEquiv B.2 (d.restrictedPartner B.1 ⟨legOfVertexLocal v i, hleg0⟩)) =
      Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B.1))
      (fun {_} hx => d.componentPartition.le B.2 hx) ⟨w, hw⟩ := by
    rw [QuarticDiagram.vertexOfLeg_blockLegEquiv]
    refine congrArg (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S)) (q := (· ∈ B.1))
      (fun {_} hx => d.componentPartition.le B.2 hx)) ?_
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
    ← hblock0, QuarticDiagram.restrictedPairing_partner_blockLegEquiv,
    QuarticDiagram.bigLegEquiv_symm_sigma_mk, hv2, hl2,
    d.equivSigmaParts_symm_subtypeSubtypeEquivSubtype B.2 w hw,
    QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]

/-- Reassembling a diagram's connected component restrictions recovers the diagram. -/
theorem QuarticDiagram.reassemble_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    QuarticDiagram.reassemble d.componentPartition
      (fun B => d.restrictComponentConnected B.2) = d := by
  refine QuarticDiagram.ext (funext d.reassemble_componentPartition_vertexLabel) ?_
  apply Combinatorics.PairingOn.ext
  apply Equiv.ext
  intro leg
  rw [← QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg]
  exact d.reassemble_componentPartition_partner (vertexOfLeg leg) (localLegOfLeg leg)

end Common
end SecondQuantization
