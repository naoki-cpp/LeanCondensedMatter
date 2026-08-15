import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentRestriction

set_option linter.style.header false

/-!
# Connectedness of restricted labelled quartic diagrams

A quartic diagram restricted to one part of its connected-component partition is connected. The
proof depends only on the pairing-induced vertex graph and is independent of vertex labels and
particle statistics.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- A vertex of component part `B`, viewed as a vertex of the ambient set `S`. -/
noncomputable def QuarticDiagram.blockVertex {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥B) : ↥S :=
  ((QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm v :
    {v : ↥S // (v : Fin N) ∈ B})

theorem QuarticDiagram.blockVertex_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥B) :
    (d.blockVertex hB v : Fin N) ∈ B :=
  (((QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm v :
    {v : ↥S // (v : Fin N) ∈ B})).2

private theorem QuarticDiagram.blockVertex_injective {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    Function.Injective (d.blockVertex hB) := fun _v _w h =>
  (QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm.injective
    (Subtype.ext h)

/-- `blockLegEquiv` maps a leg to vertex `v` exactly when its ambient vertex is `blockVertex v`. -/
theorem QuarticDiagram.vertexOfLeg_blockLegEquiv_eq_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) (v : ↥B) :
    vertexOfLeg (d.blockLegEquiv hB leg) = v ↔
      vertexOfLeg (leg : Fin (2 * (2 * S.card))) = d.blockVertex hB v := by
  rw [d.vertexOfLeg_blockLegEquiv hB leg, Equiv.apply_eq_iff_eq_symm_apply]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The restricted diagram's adjacency is the ambient adjacency transported through `blockVertex`. -/
theorem QuarticDiagram.restrictComponent_vertexGraph_adj_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (u w : ↥B) :
    (d.restrictComponent hB).vertexGraph.Adj u w ↔
      d.vertexGraph.Adj (d.blockVertex hB u) (d.blockVertex hB w) := by
  constructor
  · rintro ⟨huw, leg', hu, hw⟩
    set leg := (d.blockLegEquiv hB).symm leg' with hleg
    have hleg' : d.blockLegEquiv hB leg = leg' := Equiv.apply_symm_apply _ leg'
    rw [d.restrictComponent_pairing hB] at hw
    refine ⟨fun h => huw (d.blockVertex_injective hB h),
      (leg : Fin (2 * (2 * S.card))), ?_, ?_⟩
    · rw [← d.vertexOfLeg_blockLegEquiv_eq_iff hB leg u, hleg', hu]
    · rw [← hleg', d.restrictedPairing_partner_blockLegEquiv hB,
        d.vertexOfLeg_blockLegEquiv_eq_iff hB (d.restrictedPartner B leg) w] at hw
      rwa [d.restrictedPartner_val] at hw
  · rintro ⟨hne, leg0, hu0, hw0⟩
    have hleg0 : d.legInBlock B leg0 := by
      unfold QuarticDiagram.legInBlock
      apply (d.componentBlock_eq_iff_mem hB _).mpr
      rw [hu0]
      exact d.blockVertex_mem hB u
    refine ⟨fun h => hne (congrArg (d.blockVertex hB) h),
      d.blockLegEquiv hB ⟨leg0, hleg0⟩, ?_, ?_⟩
    · exact (d.vertexOfLeg_blockLegEquiv_eq_iff hB ⟨leg0, hleg0⟩ u).mpr hu0
    · rw [d.restrictComponent_pairing hB, d.restrictedPairing_partner_blockLegEquiv hB]
      apply (d.vertexOfLeg_blockLegEquiv_eq_iff
        hB (d.restrictedPartner B ⟨leg0, hleg0⟩) w).mpr
      rw [d.restrictedPartner_val]
      exact hw0

theorem QuarticDiagram.blockVertex_subtypeMemBlockEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) (hv : (v : Fin N) ∈ B) :
    d.blockVertex hB
        (QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨v, hv⟩) = v := by
  unfold QuarticDiagram.blockVertex
  rw [Equiv.symm_apply_apply]

theorem QuarticDiagram.subtypeMemBlockEquiv_blockVertex {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥B) :
    QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨d.blockVertex hB v, d.blockVertex_mem hB v⟩ = v :=
  Equiv.apply_symm_apply _ v

private theorem QuarticDiagram.mem_of_adj_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) {v w : ↥S}
    (h : d.vertexGraph.Adj v w) (hv : (v : Fin N) ∈ B) : (w : Fin N) ∈ B := by
  rw [← d.componentBlock_eq_iff_mem hB] at hv ⊢
  rw [← d.componentBlock_eq_of_reachable h.reachable]
  exact hv

private theorem QuarticDiagram.reachable_restrictComponent_of_walk {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) {v w : ↥S}
    (p : d.vertexGraph.Walk v w) (hv : (v : Fin N) ∈ B) :
    ∃ hw : (w : Fin N) ∈ B, (d.restrictComponent hB).vertexGraph.Reachable
      (QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨v, hv⟩)
      (QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨w, hw⟩) := by
  induction p with
  | nil => exact ⟨hv, SimpleGraph.Reachable.refl _⟩
  | cons hadj p' ih =>
    have hx := d.mem_of_adj_mem hB hadj hv
    obtain ⟨hw, hreach⟩ := ih hx
    refine ⟨hw, SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hreach⟩
    rw [d.restrictComponent_vertexGraph_adj_iff hB,
      d.blockVertex_subtypeMemBlockEquiv hB _ hv,
      d.blockVertex_subtypeMemBlockEquiv hB _ hx]
    exact hadj

/-- Restricting a diagram to a component part produces a connected diagram. -/
theorem QuarticDiagram.restrictComponent_isConnected {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).IsConnected := by
  refine ⟨fun u w => ?_, ?_⟩
  · have hw : d.componentBlock (d.blockVertex hB w) = B :=
      (d.componentBlock_eq_iff_mem hB _).2 (d.blockVertex_mem hB w)
    have hmem : (d.blockVertex hB u : Fin N) ∈ d.componentBlock (d.blockVertex hB w) := by
      rw [hw]
      exact d.blockVertex_mem hB u
    obtain ⟨hx, hreach⟩ := (d.mem_componentBlock (d.blockVertex hB w)).1 hmem
    obtain ⟨p⟩ :=
      (hreach : d.vertexGraph.Reachable (d.blockVertex hB u) (d.blockVertex hB w))
    obtain ⟨hw', hreach2⟩ :=
      d.reachable_restrictComponent_of_walk hB p (d.blockVertex_mem hB u)
    rwa [d.subtypeMemBlockEquiv_blockVertex hB u,
      d.subtypeMemBlockEquiv_blockVertex hB w] at hreach2
  · obtain ⟨x, hxS, hx⟩ := d.componentPartition.part_surjOn hB
    exact ⟨x, by rw [← hx]; exact d.componentPartition.mem_part hxS⟩

/-- `restrictComponent`, packaged as a connected labelled quartic diagram. -/
noncomputable def QuarticDiagram.restrictComponentConnected {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ConnectedQuarticDiagram Label N B :=
  ⟨d.restrictComponent hB, d.restrictComponent_isConnected hB⟩

end Common
end SecondQuantization
