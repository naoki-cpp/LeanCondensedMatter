import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ComponentPartition

set_option linter.style.header false

/-!
# Restricting a quartic Wick diagram to one connected component

Builds the smaller `QuarticWickDiagram Mode N B` a component block `B` carries, by restricting
`d`'s vertex labels and pairing to `B`'s legs. The key fact making the pairing restriction
well-defined is `legInBlock_partner_iff`: a leg's partner stays within the same component block.

Connectedness of the restricted diagram, and reassembly from a family of connected component
diagrams, are developed separately.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **A leg belongs to block `B`** iff its vertex does. -/
def QuarticWickDiagram.legInBlock {S : Finset (Fin N)} (_d : QuarticWickDiagram Mode N S)
    (B : Finset (Fin N)) (leg : Fin (2 * (2 * S.card))) : Prop :=
  (vertexOfLeg leg : Fin N) ∈ B

theorem QuarticWickDiagram.componentBlock_eq_iff_mem {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) :
    d.componentBlock v = B ↔ (v : Fin N) ∈ B :=
  ⟨fun h => h ▸ d.self_mem_componentBlock v, fun hv => by
    obtain ⟨w, rfl⟩ := d.exists_componentBlock_eq_of_mem hB
    obtain ⟨hx, hreach⟩ := (d.mem_componentBlock w).1 hv
    exact d.componentBlock_eq_of_reachable hreach⟩

/-- **Every component block is a subset of the vertex set** — a `Finpartition` part is `≤` its
whole, and `≤` on `Finset` is `⊆`. Lets every downstream construction take just `hB` rather than
both `hB` and a separately-supplied `hBS : B ⊆ S`. -/
theorem QuarticWickDiagram.componentPart_subset {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : B ⊆ S := by
  have h := Finset.le_sup (f := id) hB
  rwa [d.componentPartition.sup_parts] at h

/-- **A leg and its partner have the same vertex block.** The bridge fact connecting
`vertexGraph`'s adjacency (which pairing directly witnesses) to `componentBlock`. -/
theorem QuarticWickDiagram.componentBlock_vertexOfLeg_partner {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (leg : Fin (2 * (2 * S.card))) :
    d.componentBlock (vertexOfLeg (d.pairing.partner leg)) =
      d.componentBlock (vertexOfLeg leg) := by
  by_cases h : vertexOfLeg (d.pairing.partner leg) = vertexOfLeg leg
  · rw [h]
  · exact d.componentBlock_eq_of_reachable
      (SimpleGraph.Adj.reachable
        ⟨h, d.pairing.partner leg, rfl, by rw [d.pairing.partner_involutive]⟩)

/-- **A leg's partner stays within its block**, for a genuine component block `B`. -/
theorem QuarticWickDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card))) :
    d.legInBlock B leg ↔ d.legInBlock B (d.pairing.partner leg) := by
  unfold QuarticWickDiagram.legInBlock
  rw [← d.componentBlock_eq_iff_mem hB, ← d.componentBlock_eq_iff_mem hB,
    d.componentBlock_vertexOfLeg_partner]

/-- **The restricted partner permutation**, on the subtype of legs belonging to block `B`. -/
noncomputable def QuarticWickDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} :=
  d.pairing.partner.subtypePerm fun leg => (d.legInBlock_partner_iff hB leg).symm

theorem QuarticWickDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner hB leg : Fin (2 * (2 * S.card))) = d.pairing.partner leg :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ leg)

theorem QuarticWickDiagram.restrictedPartner_involutive {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    Function.Involutive (d.restrictedPartner hB) := fun leg => by
  apply Subtype.ext
  rw [d.restrictedPartner_val, d.restrictedPartner_val, d.pairing.partner_involutive]

theorem QuarticWickDiagram.restrictedPartner_ne_self {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    d.restrictedPartner hB leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedPartner_val hB, h])

/-- **The vertices of `S` lying in `B`, identified with `↥B`** — the subtype-of-subtype collapse
used to build `blockLegEquiv`, given `B ⊆ S`. -/
def QuarticWickDiagram.subtypeMemBlockEquiv {S : Finset (Fin N)} (B : Finset (Fin N))
    (hBS : B ⊆ S) : {v : ↥S // (v : Fin N) ∈ B} ≃ ↥B :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (· ∈ B)).trans
    (Equiv.subtypeEquivRight fun _x => ⟨fun h => h.2, fun h => ⟨hBS h, h⟩⟩)

@[simp]
theorem QuarticWickDiagram.subtypeMemBlockEquiv_symm_val {S : Finset (Fin N)}
    {B : Finset (Fin N)} (hBS : B ⊆ S) (v : ↥B) :
    (((QuarticWickDiagram.subtypeMemBlockEquiv B hBS).symm v : {v : ↥S // (v : Fin N) ∈ B}) :
      Fin N) = (v : Fin N) :=
  rfl

/-- **A leg's flattened position is recovered from its own vertex and local leg.** The round trip
`legOfVertexLocal`/`vertexOfLeg`/`localLegOfLeg` didn't state, `quarticLegEquiv`'s own
`symm_apply_apply` specialized. -/
theorem QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg {S : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card))) :
    legOfVertexLocal (vertexOfLeg leg) (localLegOfLeg leg) = leg :=
  (quarticLegEquiv S).symm_apply_apply leg

/-- **The leg-reindexing equivalence between block `B`'s legs (as a subtype of `S`'s legs) and
`B`'s own flattened leg positions `Fin (2 * (2 * B.card))`.** Built directly through
`legOfVertexLocal`/`vertexOfLeg`/`localLegOfLeg` (the same `quarticLegEquiv` convention on both
sides, per `WickDiagram.lean`'s module docstring), so vertex/local-leg identity transports by
construction (`vertexOfLeg_blockLegEquiv`/`localLegOfLeg_blockLegEquiv`), not just cardinality. -/
noncomputable def QuarticWickDiagram.blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} ≃ Fin (2 * (2 * B.card)) where
  toFun leg :=
    legOfVertexLocal
      (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))), leg.2⟩)
      (localLegOfLeg (leg : Fin (2 * (2 * S.card))))
  invFun leg' :=
    ⟨legOfVertexLocal
        (((QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm
          (vertexOfLeg leg') : {v : ↥S // (v : Fin N) ∈ B}) : ↥S)
        (localLegOfLeg leg'),
      by
        unfold QuarticWickDiagram.legInBlock
        rw [vertexOfLeg_legOfVertexLocal]
        exact (((QuarticWickDiagram.subtypeMemBlockEquiv B
          (d.componentPart_subset hB)).symm (vertexOfLeg leg') :
            {v : ↥S // (v : Fin N) ∈ B})).2⟩
  left_inv leg := by
    apply Subtype.ext
    simp [Equiv.symm_apply_apply, QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]
  right_inv leg' := by
    simp [Equiv.apply_symm_apply, QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]

/-- **`blockLegEquiv` preserves each leg's vertex**, exactly (not merely its ambient `Fin N`
value): the restricted diagram's vertex, viewed back in `S` via `subtypeMemBlockEquiv`, is the
original leg's own vertex. -/
theorem QuarticWickDiagram.vertexOfLeg_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    vertexOfLeg (d.blockLegEquiv hB leg) =
      QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))), leg.2⟩ :=
  vertexOfLeg_legOfVertexLocal _ _

/-- **`blockLegEquiv` preserves each leg's local leg.** -/
theorem QuarticWickDiagram.localLegOfLeg_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    localLegOfLeg (d.blockLegEquiv hB leg) = localLegOfLeg (leg : Fin (2 * (2 * S.card))) :=
  localLegOfLeg_legOfVertexLocal _ _

private theorem permCongr_partner_involutive {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : Function.Involutive p) : Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem permCongr_partner_ne_self {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α)
    (hp : ∀ x, p x ≠ x) (x : β) : e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- **The restricted pairing `Pairing (2 * B.card)` on block `B`'s `4 * B.card` legs.** -/
noncomputable def QuarticWickDiagram.restrictedPairing {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    Common.BlochDeDominicis.Pairing (2 * B.card) :=
  Common.BlochDeDominicis.Pairing.ofPartner
    ((d.blockLegEquiv hB).permCongr (d.restrictedPartner hB))
    ⟨permCongr_partner_involutive _ _ (d.restrictedPartner_involutive hB),
      permCongr_partner_ne_self _ _ (d.restrictedPartner_ne_self hB)⟩

/-- **`restrictedPairing`'s partner agrees with `d`'s own partner**, transported along
`blockLegEquiv`. The fact needed to compare the restricted diagram's `vertexGraph` to `d`'s own
graph restricted to `B`. -/
theorem QuarticWickDiagram.restrictedPairing_partner_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPairing hB).partner (d.blockLegEquiv hB leg) =
      d.blockLegEquiv hB (d.restrictedPartner hB leg) := by
  simp [restrictedPairing, Common.BlochDeDominicis.Pairing.ofPartner, Equiv.permCongr_apply]

/-- **The restriction of `d` to component block `B`.** -/
noncomputable def QuarticWickDiagram.restrictComponent {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    QuarticWickDiagram Mode N B where
  vertexLabel v :=
    d.vertexLabel ((QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm
      v).1
  pairing := d.restrictedPairing hB

theorem QuarticWickDiagram.restrictComponent_pairing {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)} (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).pairing = d.restrictedPairing hB := rfl

end SecondQuantization
