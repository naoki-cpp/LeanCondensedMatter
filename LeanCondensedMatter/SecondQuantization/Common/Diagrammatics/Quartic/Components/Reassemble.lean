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
private theorem QuarticDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)}
    (π : Finpartition S) (v : ↥S) (i : Fin 4) :
    QuarticDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  have hqv : quarticLegEquiv S (legOfVertexLocal v i) = (v, i) :=
    Equiv.apply_symm_apply (quarticLegEquiv S) (v, i)
  simp only [QuarticDiagram.bigLegEquiv, Equiv.trans_apply, hqv, Equiv.prodCongr_apply,
    Equiv.sigmaProdDistrib_apply, Equiv.sigmaCongrRight_apply]
  rfl

/-- The inverse of `bigLegEquiv` at a leg belonging to one partition part. -/
private theorem QuarticDiagram.bigLegEquiv_symm_sigma_mk {S : Finset (Fin N)}
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

/-- Reassemble an ambient labelled quartic diagram from connected diagrams on partition parts. -/
noncomputable def QuarticDiagram.reassemble {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    QuarticDiagram Label N S where
  vertexLabel v := (F (π.equivSigmaParts v).1).1.vertexLabel (π.equivSigmaParts v).2
  pairing :=
    (Combinatorics.PairingOn.sigmaCongrRight fun B => (F B).1.pairing).transport
      (QuarticDiagram.bigLegEquiv π)


private theorem QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts) (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticDiagram.reassemble π F).pairing.partner
        ((QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩) =
      (QuarticDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
  simp [QuarticDiagram.reassemble]

/-- A vertex of a block `B`, included back into the ambient vertex set. -/
private noncomputable def QuarticDiagram.reassembleVertex {S : Finset (Fin N)} (π : Finpartition S)
    (B : π.parts) (v : ↥(B : Finset (Fin N))) : ↥S :=
  π.equivSigmaParts.symm ⟨B, v⟩

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
  change (QuarticDiagram.bigLegEquiv π
      (((Combinatorics.PairingOn.sigmaCongrRight fun B => (F B).1.pairing).transport
        (QuarticDiagram.bigLegEquiv π)).partner leg)).1 =
    (QuarticDiagram.bigLegEquiv π leg).1
  rw [Combinatorics.PairingOn.transport_partner, Equiv.apply_symm_apply]
  cases h : QuarticDiagram.bigLegEquiv π leg with
  | mk B p =>
    simp only [Combinatorics.PairingOn.sigmaCongrRight_partner]

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
  simpa only [Relation.reflTransGen_eq_self] using
    (Relation.ReflTransGen.lift (p := Eq)
      (fun v : ↥S => π.part (v : Fin N))
      (fun _ _ hadj => QuarticDiagram.reassemble_vertexGraph_adj_same_part π F hadj))
      ((SimpleGraph.reachable_iff_reflTransGen u w).mp h)

private theorem QuarticDiagram.reassemble_componentBlock_subset_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (v : ↥S) :
    (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn v ⊆ π.part (v : Fin N) := by
  intro x hx
  change x ∈ (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn v at hx
  obtain ⟨hxS, hreach⟩ :=
    ((QuarticDiagram.reassemble π F).vertexGraph.mem_componentBlockOn v).1 hx
  rw [← QuarticDiagram.reassemble_reachable_same_part π F hreach]
  exact π.mem_part hxS

/-- The inclusion of a reassembled component preserves vertex adjacency. -/
private noncomputable def QuarticDiagram.reassembleComponentHom {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts) :
    (F B).1.vertexGraph →g (QuarticDiagram.reassemble π F).vertexGraph where
  toFun := QuarticDiagram.reassembleVertex π B
  map_rel' := by
    intro u' w' h
    obtain ⟨hne', leg, hu', hw'⟩ := h
    set leg0 := (QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩ with hlegdef
    have hu : vertexOfLeg leg0 = QuarticDiagram.reassembleVertex π B u' := by
      rw [hlegdef, QuarticDiagram.bigLegEquiv_symm_sigma_mk]
      rw [vertexOfLeg_legOfVertexLocal, hu']
      rfl
    have hpartner :
        (QuarticDiagram.reassemble π F).pairing.partner leg0 =
          (QuarticDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
      rw [hlegdef]
      exact QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk π F B leg
    have hw : vertexOfLeg ((QuarticDiagram.reassemble π F).pairing.partner leg0) =
        QuarticDiagram.reassembleVertex π B w' := by
      rw [hpartner, QuarticDiagram.bigLegEquiv_symm_sigma_mk]
      rw [vertexOfLeg_legOfVertexLocal, hw']
      rfl
    refine ⟨?_, leg0, hu, hw⟩
    intro hEq
    apply hne'
    apply Subtype.ext
    exact congrArg (fun v : ↥S => (v : Fin N)) hEq

private theorem QuarticDiagram.part_subset_reassemble_componentBlock
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (v : ↥S) :
    π.part (v : Fin N) ⊆ (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn v := by
  intro x hx
  set B := (π.equivSigmaParts v).1
  have hxB : x ∈ (B : Finset (Fin N)) := hx
  have hxS : x ∈ S := π.le B.2 hxB
  have hreach0 : (F B).1.vertexGraph.Reachable (⟨x, hxB⟩ : ↥(B : Finset (Fin N)))
      (π.equivSigmaParts v).2 :=
    (F B).2.1 ⟨x, hxB⟩ (π.equivSigmaParts v).2
  have hreach := hreach0.map (QuarticDiagram.reassembleComponentHom π F B)
  change (QuarticDiagram.reassemble π F).vertexGraph.Reachable
    (QuarticDiagram.reassembleVertex π B ⟨x, hxB⟩)
    (QuarticDiagram.reassembleVertex π B (π.equivSigmaParts v).2) at hreach
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
    (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn v = π.part (v : Fin N) :=
  Finset.Subset.antisymm (QuarticDiagram.reassemble_componentBlock_subset_part π F v)
    (QuarticDiagram.part_subset_reassemble_componentBlock π F v)

/-- The component partition of a reassembled family is the original partition. -/
theorem QuarticDiagram.componentPartition_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn = π := by
  apply Finpartition.ext
  apply Finset.Subset.antisymm
  · intro B hB
    obtain ⟨v, hvS, hv⟩ :=
      (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.part_surjOn hB
    have hblock :
        (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn (⟨v, hvS⟩ : ↥S) = B := by
      simpa only [SimpleGraph.componentBlockOn] using hv
    rw [← hblock, QuarticDiagram.reassemble_componentBlock_eq_part]
    exact π.part_mem.2 hvS
  · intro B hB
    obtain ⟨v, hvS, hv⟩ := π.part_surjOn hB
    have hmem :
        (QuarticDiagram.reassemble π F).vertexGraph.componentBlockOn (⟨v, hvS⟩ : ↥S) ∈
          (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.parts := by
      unfold SimpleGraph.componentBlockOn
      exact (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.part_mem.2 hvS
    rwa [QuarticDiagram.reassemble_componentBlock_eq_part, hv] at hmem

private theorem QuarticDiagram.restrictComponent_reassemble_vertexLabel
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.parts)
    (v : ↥(B : Finset (Fin N))) :
    ((QuarticDiagram.reassemble π F).restrictComponent hB').vertexLabel v =
      (F B).1.vertexLabel v := by
  set u := (((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
    (q := (· ∈ (B : Finset (Fin N))))
    (fun {_} hx => (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.le hB' hx)).symm v : ↥S))
  change (F (π.equivSigmaParts u).1).1.vertexLabel (π.equivSigmaParts u).2 =
      (F B).1.vertexLabel v
  have hueq : u = π.equivSigmaParts.symm ⟨B, v⟩ := by
    apply Subtype.ext
    rfl
  rw [hueq, Equiv.apply_symm_apply]

/-- The component-local inclusion of a leg agrees with the partition-wide inclusion
for any partition containing the same block. -/
private theorem QuarticDiagram.blockLegEquiv_symm_val_bigLegEquiv
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (π : Finpartition S) (B : π.parts)
    (hB : (B : Finset (Fin N)) ∈ d.vertexGraph.componentPartitionOn.parts)
    (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((d.blockLegEquiv hB).symm leg).1 =
      (QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩ := by
  rw [QuarticDiagram.bigLegEquiv_symm_sigma_mk]
  change legOfVertexLocal
      ((((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ S))
        (q := (· ∈ (B : Finset (Fin N))))
        (fun {_} hx => d.vertexGraph.componentPartitionOn.le hB hx)).symm
          (vertexOfLeg leg) : {v : ↥S // (v : Fin N) ∈ (B : Finset (Fin N))}) : ↥S))
      (localLegOfLeg leg) =
    legOfVertexLocal
      (π.equivSigmaParts.symm ⟨B, vertexOfLeg leg⟩)
      (localLegOfLeg leg)
  apply congrArg (fun v : ↥S => legOfVertexLocal v (localLegOfLeg leg))
  apply Subtype.ext
  rfl

private theorem QuarticDiagram.restrictComponent_reassemble_pairing
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.parts) :
    ((QuarticDiagram.reassemble π F).restrictComponent hB').pairing = (F B).1.pairing := by
  let d := QuarticDiagram.reassemble π F
  change d.restrictedPairing hB' = (F B).1.pairing
  apply Combinatorics.PairingOn.ext
  apply Equiv.ext
  intro leg
  apply (d.blockLegEquiv hB').symm.injective
  apply Subtype.ext
  have hrestricted := d.pairing.restrictAlongEquiv_partner_symm_val
    (d.legInBlock (B : Finset (Fin N)))
    (fun i => d.legInBlock_partner_iff i) (d.blockLegEquiv hB') leg
  change
    ((d.blockLegEquiv hB').symm ((d.restrictedPairing hB').partner leg)).1 =
      d.pairing.partner ((d.blockLegEquiv hB').symm leg) at hrestricted
  calc
    ((d.blockLegEquiv hB').symm ((d.restrictedPairing hB').partner leg)).1 =
        d.pairing.partner ((d.blockLegEquiv hB').symm leg) := hrestricted
    _ = d.pairing.partner ((QuarticDiagram.bigLegEquiv π).symm ⟨B, leg⟩) := by
      rw [d.blockLegEquiv_symm_val_bigLegEquiv π B hB' leg]
    _ = (QuarticDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ :=
      QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk π F B leg
    _ = ((d.blockLegEquiv hB').symm ((F B).1.pairing.partner leg)).1 :=
      (d.blockLegEquiv_symm_val_bigLegEquiv π B hB'
        ((F B).1.pairing.partner leg)).symm

/-- Restricting a reassembled diagram to one partition block recovers that block's diagram. -/
theorem QuarticDiagram.restrictComponent_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).vertexGraph.componentPartitionOn.parts) :
    (QuarticDiagram.reassemble π F).restrictComponent hB' = (F B).1 := by
  refine QuarticDiagram.ext
    (funext fun v =>
      QuarticDiagram.restrictComponent_reassemble_vertexLabel π F B hB' v) ?_
  exact QuarticDiagram.restrictComponent_reassemble_pairing π F B hB'

private theorem QuarticDiagram.reassemble_componentPartition_vertexLabel
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (v : ↥S) :
    (QuarticDiagram.reassemble d.vertexGraph.componentPartitionOn
      fun B => d.restrictComponentConnected B.2).vertexLabel v = d.vertexLabel v := by
  let π := d.vertexGraph.componentPartitionOn
  change (d.restrictComponent (π.equivSigmaParts v).1.2).vertexLabel
    (π.equivSigmaParts v).2 = d.vertexLabel v
  rw [d.restrictComponent_vertexLabel_equivSigmaParts]
  have hη :
      (⟨(π.equivSigmaParts v).1, (π.equivSigmaParts v).2⟩ :
        Σ B : π.parts, ↥(B : Finset (Fin N))) = π.equivSigmaParts v := by
    cases π.equivSigmaParts v
    rfl
  rw [hη, Equiv.symm_apply_apply]

private theorem QuarticDiagram.reassemble_componentPartition_partner
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (leg : Fin (2 * (2 * S.card))) :
    (QuarticDiagram.reassemble d.vertexGraph.componentPartitionOn
        fun B => d.restrictComponentConnected B.2).pairing.partner leg =
      d.pairing.partner leg := by
  let π := d.vertexGraph.componentPartitionOn
  have h (q : Σ B : π.parts, Fin (2 * (2 * (B : Finset (Fin N)).card))) :
      (QuarticDiagram.reassemble π
          fun B => d.restrictComponentConnected B.2).pairing.partner
          ((QuarticDiagram.bigLegEquiv π).symm q) =
        d.pairing.partner ((QuarticDiagram.bigLegEquiv π).symm q) := by
    obtain ⟨B, p⟩ := q
    rw [QuarticDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk]
    change (QuarticDiagram.bigLegEquiv π).symm
        ⟨B, (d.restrictedPairing B.2).partner p⟩ =
      d.pairing.partner ((QuarticDiagram.bigLegEquiv π).symm ⟨B, p⟩)
    rw [← d.blockLegEquiv_symm_val_bigLegEquiv π B B.2
        ((d.restrictedPairing B.2).partner p),
      ← d.blockLegEquiv_symm_val_bigLegEquiv π B B.2 p]
    exact d.pairing.restrictAlongEquiv_partner_symm_val
      (d.legInBlock (B : Finset (Fin N))) (fun j => d.legInBlock_partner_iff j)
      (d.blockLegEquiv B.2) p
  simpa only [Equiv.symm_apply_apply] using
    h (QuarticDiagram.bigLegEquiv π leg)

/-- Reassembling a diagram's connected component restrictions recovers the diagram. -/
theorem QuarticDiagram.reassemble_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    QuarticDiagram.reassemble d.vertexGraph.componentPartitionOn
      (fun B => d.restrictComponentConnected B.2) = d := by
  refine QuarticDiagram.ext (funext d.reassemble_componentPartition_vertexLabel) ?_
  apply Combinatorics.PairingOn.ext
  apply Equiv.ext
  intro leg
  exact d.reassemble_componentPartition_partner leg

end Common
end SecondQuantization
