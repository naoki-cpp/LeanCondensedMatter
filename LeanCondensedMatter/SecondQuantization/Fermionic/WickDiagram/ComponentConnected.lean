import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ComponentRestriction

set_option linter.style.header false

/-!
# `restrictComponent`'s result is connected

Proves `d.restrictComponent hB` is a genuine `ConnectedQuarticWickDiagram Mode N B`: its
`vertexGraph`'s adjacency exactly mirrors `d.vertexGraph`'s adjacency restricted to `B`
(`restrictComponent_vertexGraph_adj_iff`), and every walk in `d.vertexGraph` starting inside `B`
stays inside `B` (since `B` is a full reachability class), so reachability inside `B` for `d`
transports to reachability in the restricted graph.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`B`'s vertices, identified back with `↥S`.** -/
noncomputable def QuarticWickDiagram.blockVertex {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (v : ↥B) : ↥S :=
  ((QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm v :
    {v : ↥S // (v : Fin N) ∈ B})

theorem QuarticWickDiagram.blockVertex_mem {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) (v : ↥B) :
    (d.blockVertex hB v : Fin N) ∈ B :=
  (((QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm v :
    {v : ↥S // (v : Fin N) ∈ B})).2

private theorem QuarticWickDiagram.blockVertex_injective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    Function.Injective (d.blockVertex hB) := fun _v _w h =>
  (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm.injective
    (Subtype.ext h)

/-- **A leg's `blockLegEquiv`-image has vertex `v` iff the leg itself has vertex `blockVertex v`.**
The bridge between `S`-level and `B`-level vertex identities `blockLegEquiv` transports. -/
theorem QuarticWickDiagram.vertexOfLeg_blockLegEquiv_eq_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) (v : ↥B) :
    vertexOfLeg (d.blockLegEquiv hB leg) = v ↔
      vertexOfLeg (leg : Fin (2 * (2 * S.card))) = d.blockVertex hB v := by
  rw [d.vertexOfLeg_blockLegEquiv hB leg, Equiv.apply_eq_iff_eq_symm_apply]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- **`restrictComponent`'s `vertexGraph` adjacency is exactly `d`'s own, read through
`blockVertex`.** -/
theorem QuarticWickDiagram.restrictComponent_vertexGraph_adj_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (u w : ↥B) :
    (d.restrictComponent hB).vertexGraph.Adj u w ↔
      d.vertexGraph.Adj (d.blockVertex hB u) (d.blockVertex hB w) := by
  constructor
  · rintro ⟨huw, leg', hu, hw⟩
    set leg := (d.blockLegEquiv hB).symm leg' with hleg
    have hleg' : d.blockLegEquiv hB leg = leg' := Equiv.apply_symm_apply _ leg'
    rw [d.restrictComponent_pairing hB] at hw
    refine ⟨fun h => huw (d.blockVertex_injective hB h), (leg : Fin (2 * (2 * S.card))), ?_, ?_⟩
    · rw [← d.vertexOfLeg_blockLegEquiv_eq_iff hB leg u, hleg', hu]
    · rw [← hleg', d.restrictedPairing_partner_blockLegEquiv hB,
        d.vertexOfLeg_blockLegEquiv_eq_iff hB (d.restrictedPartner hB leg) w] at hw
      rwa [d.restrictedPartner_val] at hw
  · rintro ⟨hne, leg0, hu0, hw0⟩
    have hleg0 : d.legInBlock B leg0 := by
      rw [QuarticWickDiagram.legInBlock, hu0]
      exact d.blockVertex_mem hB u
    refine ⟨fun h => hne (congrArg (d.blockVertex hB) h), d.blockLegEquiv hB ⟨leg0, hleg0⟩, ?_, ?_⟩
    · exact (d.vertexOfLeg_blockLegEquiv_eq_iff hB ⟨leg0, hleg0⟩ u).mpr hu0
    · rw [d.restrictComponent_pairing hB, d.restrictedPairing_partner_blockLegEquiv hB]
      apply (d.vertexOfLeg_blockLegEquiv_eq_iff hB (d.restrictedPartner hB ⟨leg0, hleg0⟩) w).mpr
      rw [d.restrictedPartner_val]
      exact hw0

theorem QuarticWickDiagram.blockVertex_subtypeMemBlockEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (v : ↥S) (hv : (v : Fin N) ∈ B) :
    d.blockVertex hB
        (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨v, hv⟩) = v := by
  unfold QuarticWickDiagram.blockVertex
  rw [Equiv.symm_apply_apply]

theorem QuarticWickDiagram.subtypeMemBlockEquiv_blockVertex {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (v : ↥B) :
    QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨d.blockVertex hB v, d.blockVertex_mem hB v⟩ = v :=
  Equiv.apply_symm_apply _ v

/-- **Adjacency preserves membership in `B`**, for a genuine component block `B` — the reason a
walk starting inside `B` never leaves it. -/
private theorem QuarticWickDiagram.mem_of_adj_mem {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    {v w : ↥S}
    (h : d.vertexGraph.Adj v w) (hv : (v : Fin N) ∈ B) : (w : Fin N) ∈ B := by
  rw [← d.componentBlock_eq_iff_mem hB] at hv ⊢
  rw [← d.componentBlock_eq_of_reachable h.reachable]
  exact hv

/-- **Every walk of `d.vertexGraph` starting inside `B` stays inside `B`, and transports to a
walk of the restricted graph.** Proved by induction on the walk. -/
private theorem QuarticWickDiagram.reachable_restrictComponent_of_walk {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    {v w : ↥S} (p : d.vertexGraph.Walk v w) (hv : (v : Fin N) ∈ B) :
    ∃ hw : (w : Fin N) ∈ B, (d.restrictComponent hB).vertexGraph.Reachable
      (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨v, hv⟩)
      (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨w, hw⟩) := by
  induction p with
  | nil => exact ⟨hv, SimpleGraph.Reachable.refl _⟩
  | cons hadj p' ih =>
    have hx := d.mem_of_adj_mem hB hadj hv
    obtain ⟨hw, hreach⟩ := ih hx
    refine ⟨hw, SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hreach⟩
    rw [d.restrictComponent_vertexGraph_adj_iff hB,
      d.blockVertex_subtypeMemBlockEquiv hB _ hv, d.blockVertex_subtypeMemBlockEquiv hB _ hx]
    exact hadj

/-- **`restrictComponent`'s result is connected.** -/
theorem QuarticWickDiagram.restrictComponent_isConnected {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).IsConnected := by
  refine ⟨fun u w => ?_, ?_⟩
  · have hw : d.componentBlock (d.blockVertex hB w) = B :=
      (d.componentBlock_eq_iff_mem hB _).2 (d.blockVertex_mem hB w)
    have hmem : (d.blockVertex hB u : Fin N) ∈ d.componentBlock (d.blockVertex hB w) := by
      rw [hw]; exact d.blockVertex_mem hB u
    obtain ⟨hx, hreach⟩ := (d.mem_componentBlock (d.blockVertex hB w)).1 hmem
    obtain ⟨p⟩ := (hreach : d.vertexGraph.Reachable (d.blockVertex hB u) (d.blockVertex hB w))
    obtain ⟨hw', hreach2⟩ := d.reachable_restrictComponent_of_walk hB p (d.blockVertex_mem hB u)
    rwa [d.subtypeMemBlockEquiv_blockVertex hB u, d.subtypeMemBlockEquiv_blockVertex hB w]
      at hreach2
  · obtain ⟨v, rfl⟩ := d.exists_componentBlock_eq_of_mem hB
    exact ⟨v, d.self_mem_componentBlock v⟩

/-- **`restrictComponent`, packaged as a genuine `ConnectedQuarticWickDiagram`.** -/
noncomputable def QuarticWickDiagram.restrictComponentConnected {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    ConnectedQuarticWickDiagram Mode N B :=
  ⟨d.restrictComponent hB, d.restrictComponent_isConnected hB⟩

end SecondQuantization
