import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPartition
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentRestriction

set_option linter.style.header false

/-!
# Restricting a labelled quartic diagram to one connected component

The restriction construction depends only on the pairing-induced vertex graph and quartic leg
indexing. It is independent of the vertex-label type and particle statistics.

Component-leg partner invariance and pairing restriction are owned by
`Combinatorics.PerfectPairing.ComponentRestriction`; this module supplies only the quartic component
classifier and its quartic-leg reindexing. Connectedness of the restricted diagram and reassembly are
developed separately.
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
    change d.componentPartition.part (v : Fin N) = B
    exact d.componentPartition.part_eq_of_mem hB hv⟩

/-- Every component part is contained in the ambient vertex set. -/
theorem QuarticDiagram.componentPart_subset {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : B ⊆ S := by
  have h := Finset.le_sup (f := id) hB
  rwa [d.componentPartition.sup_parts] at h

/-- A leg's partner stays inside the same component part. -/
theorem QuarticDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card))) :
    d.legInBlock B leg ↔ d.legInBlock B (d.pairing.partner leg) := by
  change d.pairing.legInComponent vertexOfLeg d.componentBlock B leg ↔
    d.pairing.legInComponent vertexOfLeg d.componentBlock B (d.pairing.partner leg)
  exact d.pairing.legInComponent_partner_iff vertexOfLeg d.componentBlock
    d.componentBlock_eq_of_reachable B leg

/-- The partner permutation restricted to legs belonging to component part `B`. -/
noncomputable def QuarticDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N)) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} :=
  d.pairing.componentPartnerSubtypePerm vertexOfLeg d.componentBlock
    d.componentBlock_eq_of_reachable B

theorem QuarticDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N))
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card))) = d.pairing.partner leg := by
  change
    ((d.pairing.componentPartnerSubtypePerm vertexOfLeg d.componentBlock
      d.componentBlock_eq_of_reachable B leg) : Fin (2 * (2 * S.card))) =
        d.pairing.partner leg
  exact d.pairing.componentPartnerSubtypePerm_val vertexOfLeg d.componentBlock
    d.componentBlock_eq_of_reachable B leg

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
  d.pairing.restrictComponentAlongEquiv vertexOfLeg d.componentBlock
    d.componentBlock_eq_of_reachable B (d.blockLegEquiv hB)

/-- The restricted pairing agrees with the original partner under `blockLegEquiv`. -/
theorem QuarticDiagram.restrictedPairing_partner_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPairing hB).partner (d.blockLegEquiv hB leg) =
      d.blockLegEquiv hB (d.restrictedPartner B leg) := by
  change
    (d.pairing.restrictComponentAlongEquiv vertexOfLeg d.componentBlock
      d.componentBlock_eq_of_reachable B (d.blockLegEquiv hB)).partner
        (d.blockLegEquiv hB leg) =
      d.blockLegEquiv hB
        (d.pairing.componentPartnerSubtypePerm vertexOfLeg d.componentBlock
          d.componentBlock_eq_of_reachable B leg)
  exact d.pairing.restrictComponentAlongEquiv_partner vertexOfLeg d.componentBlock
    d.componentBlock_eq_of_reachable B (d.blockLegEquiv hB) leg

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
