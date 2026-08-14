import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPartition

set_option linter.style.header false

/-!
# Restricting a labelled quartic diagram to one connected component

The restriction construction depends only on the pairing-induced vertex graph and quartic leg
indexing. It is independent of the vertex-label type and particle statistics.

Connectedness of the restricted diagram and reassembly are developed separately.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- A leg belongs to block `B` when the connected component of its incident vertex is `B`.
For an actual part of `d.componentPartition`, this is equivalent to vertex membership in `B`. -/
def QuarticDiagram.legInBlock {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : Finset (Fin N)) (leg : Fin (2 * (2 * S.card))) : Prop :=
  d.componentBlock (vertexOfLeg leg) = B

theorem QuarticDiagram.componentBlock_eq_iff_mem {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) :
    d.componentBlock v = B ↔ (v : Fin N) ∈ B :=
  ⟨fun h => h ▸ d.self_mem_componentBlock v, fun hv => by
    obtain ⟨w, rfl⟩ := d.exists_componentBlock_eq_of_mem hB
    obtain ⟨hx, hreach⟩ := (d.mem_componentBlock w).1 hv
    exact d.componentBlock_eq_of_reachable hreach⟩

/-- Every component part is contained in the ambient vertex set. -/
theorem QuarticDiagram.componentPart_subset {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : B ⊆ S := by
  have h := Finset.le_sup (f := id) hB
  rwa [d.componentPartition.sup_parts] at h

/-- A leg and its partner have the same connected-component block. -/
theorem QuarticDiagram.componentBlock_vertexOfLeg_partner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (leg : Fin (2 * (2 * S.card))) :
    d.componentBlock (vertexOfLeg (d.pairing.partner leg)) =
      d.componentBlock (vertexOfLeg leg) := by
  by_cases h : vertexOfLeg (d.pairing.partner leg) = vertexOfLeg leg
  · rw [h]
  · exact d.componentBlock_eq_of_reachable
      (SimpleGraph.Adj.reachable
        ⟨h, d.pairing.partner leg, rfl, by rw [d.pairing.partner_involutive]⟩)

/-- A leg's partner stays inside the same component part. -/
theorem QuarticDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card))) :
    d.legInBlock B leg ↔ d.legInBlock B (d.pairing.partner leg) := by
  unfold QuarticDiagram.legInBlock
  rw [d.componentBlock_vertexOfLeg_partner]

/-- The partner permutation restricted to legs belonging to component part `B`. -/
noncomputable def QuarticDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N)) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} :=
  d.pairing.partner.subtypePerm fun leg => (d.legInBlock_partner_iff leg).symm

theorem QuarticDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N))
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card))) = d.pairing.partner leg :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ leg)

theorem QuarticDiagram.restrictedPartner_involutive {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N)) :
    Function.Involutive (d.restrictedPartner B) := fun leg => by
  apply Subtype.ext
  rw [d.restrictedPartner_val, d.restrictedPartner_val, d.pairing.partner_involutive]

theorem QuarticDiagram.restrictedPartner_ne_self {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N))
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    d.restrictedPartner B leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedPartner_val B, h])

/-- Vertices of `S` lying in `B`, identified with `↥B`. -/
def QuarticDiagram.subtypeMemBlockEquiv {S : Finset (Fin N)} (B : Finset (Fin N))
    (hBS : B ⊆ S) : {v : ↥S // (v : Fin N) ∈ B} ≃ ↥B :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (· ∈ B)).trans
    (Equiv.subtypeEquivRight fun _x => ⟨fun h => h.2, fun h => ⟨hBS h, h⟩⟩)

@[simp]
theorem QuarticDiagram.subtypeMemBlockEquiv_symm_val {S : Finset (Fin N)}
    {B : Finset (Fin N)} (hBS : B ⊆ S) (v : ↥B) :
    (((QuarticDiagram.subtypeMemBlockEquiv B hBS).symm v :
      {v : ↥S // (v : Fin N) ∈ B}) : Fin N) = (v : Fin N) :=
  rfl

/-- Reconstructing a flattened leg from its vertex and local leg is the identity. -/
theorem QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg {S : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card))) :
    legOfVertexLocal (vertexOfLeg leg) (localLegOfLeg leg) = leg :=
  (quarticLegEquiv S).symm_apply_apply leg

/-- Reindex the legs belonging to `B` as the flattened legs of the restricted diagram. -/
noncomputable def QuarticDiagram.blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} ≃ Fin (2 * (2 * B.card)) where
  toFun leg :=
    legOfVertexLocal
      (QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))),
          (d.componentBlock_eq_iff_mem hB _).mp leg.2⟩)
      (localLegOfLeg (leg : Fin (2 * (2 * S.card))))
  invFun leg' :=
    ⟨legOfVertexLocal
        (((QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm
          (vertexOfLeg leg') : {v : ↥S // (v : Fin N) ∈ B}) : ↥S)
        (localLegOfLeg leg'),
      by
        unfold QuarticDiagram.legInBlock
        rw [vertexOfLeg_legOfVertexLocal]
        apply (d.componentBlock_eq_iff_mem hB _).mpr
        exact (((QuarticDiagram.subtypeMemBlockEquiv B
          (d.componentPart_subset hB)).symm (vertexOfLeg leg') :
            {v : ↥S // (v : Fin N) ∈ B})).2⟩
  left_inv leg := by
    apply Subtype.ext
    simp [Equiv.symm_apply_apply, QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]
  right_inv leg' := by
    simp [Equiv.apply_symm_apply, QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg]

/-- `blockLegEquiv` preserves the vertex of each leg. -/
theorem QuarticDiagram.vertexOfLeg_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    vertexOfLeg (d.blockLegEquiv hB leg) =
      QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))),
          (d.componentBlock_eq_iff_mem hB _).mp leg.2⟩ :=
  vertexOfLeg_legOfVertexLocal _ _

/-- `blockLegEquiv` preserves the local leg index. -/
theorem QuarticDiagram.localLegOfLeg_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    localLegOfLeg (d.blockLegEquiv hB leg) =
      localLegOfLeg (leg : Fin (2 * (2 * S.card))) :=
  localLegOfLeg_legOfVertexLocal _ _

/-- The pairing induced on the legs of component part `B`. -/
noncomputable def QuarticDiagram.restrictedPairing {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    Combinatorics.Pairing (2 * B.card) :=
  Combinatorics.Pairing.ofPartner
    ((d.blockLegEquiv hB).permCongr (d.restrictedPartner B))
    (IsPairing.permCongr
      ⟨d.restrictedPartner_involutive B, d.restrictedPartner_ne_self B⟩
      (d.blockLegEquiv hB))

/-- The restricted pairing agrees with the original partner under `blockLegEquiv`. -/
theorem QuarticDiagram.restrictedPairing_partner_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPairing hB).partner (d.blockLegEquiv hB leg) =
      d.blockLegEquiv hB (d.restrictedPartner B leg) := by
  simp [restrictedPairing, Combinatorics.Pairing.ofPartner, Equiv.permCongr_apply]

/-- Restrict `d` to the connected-component part `B`. -/
noncomputable def QuarticDiagram.restrictComponent {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : QuarticDiagram Label N B where
  vertexLabel v :=
    d.vertexLabel ((QuarticDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm v).1
  pairing := d.restrictedPairing hB

theorem QuarticDiagram.restrictComponent_pairing {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).pairing = d.restrictedPairing hB :=
  rfl

end Common
end SecondQuantization
