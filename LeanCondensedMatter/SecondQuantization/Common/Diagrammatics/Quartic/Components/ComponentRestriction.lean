import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentPartition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.SubsetSplit

set_option linter.style.header false

/-!
# Restricting a labelled quartic diagram to one connected component

The restriction construction depends only on the pairing-induced vertex graph and quartic leg
indexing. It is independent of the vertex-label type and particle statistics.

Partner-invariant pairing restriction is owned by `Combinatorics.PerfectPairing.Restriction`; this
module supplies only the quartic component predicate and its leg reindexing. Connectedness of the
restricted diagram and reassembly are developed separately.
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

/-- A leg's partner stays inside the same component part. -/
theorem QuarticDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card))) :
    d.legInBlock B leg ↔ d.legInBlock B (d.pairing.partner leg) := by
  unfold QuarticDiagram.legInBlock
  have hEq :
      d.componentBlock (vertexOfLeg leg) =
        d.componentBlock (vertexOfLeg (d.pairing.partner leg)) := by
    change d.vertexGraph.componentBlockOn (vertexOfLeg leg) =
      d.vertexGraph.componentBlockOn (vertexOfLeg (d.pairing.partner leg))
    exact d.vertexGraph.componentBlockOn_eq_of_reachable
      (d.pairing.vertexGraph_reachable_partner vertexOfLeg leg).symm
  rw [hEq]

/-- The partner permutation restricted to legs belonging to component part `B`. -/
noncomputable def QuarticDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N)) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} :=
  d.pairing.partnerSubtypePerm (d.legInBlock B) fun leg => d.legInBlock_partner_iff leg

theorem QuarticDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N))
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card))) = d.pairing.partner leg := by
  simpa only [QuarticDiagram.restrictedPartner] using
    d.pairing.partnerSubtypePerm_val (d.legInBlock B)
      (fun i => d.legInBlock_partner_iff i) leg

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
      (Combinatorics.subsetSubtypeEquiv B (d.componentPartition.le hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))),
          (d.componentPartition.part_eq_iff_mem hB).mp leg.2⟩)
      (localLegOfLeg (leg : Fin (2 * (2 * S.card))))
  invFun leg' :=
    ⟨legOfVertexLocal
        (((Combinatorics.subsetSubtypeEquiv B (d.componentPartition.le hB)).symm
          (vertexOfLeg leg') : {v : ↥S // (v : Fin N) ∈ B}) : ↥S)
        (localLegOfLeg leg'),
      by
        unfold QuarticDiagram.legInBlock QuarticDiagram.componentBlock
        rw [vertexOfLeg_legOfVertexLocal]
        apply (d.componentPartition.part_eq_iff_mem hB).mpr
        exact (((Combinatorics.subsetSubtypeEquiv B
          (d.componentPartition.le hB)).symm (vertexOfLeg leg') :
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
      Combinatorics.subsetSubtypeEquiv B (d.componentPartition.le hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))),
          (d.componentPartition.part_eq_iff_mem hB).mp leg.2⟩ :=
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
  d.pairing.restrictAlongEquiv (d.legInBlock B)
    (fun leg => d.legInBlock_partner_iff leg) (d.blockLegEquiv hB)

/-- The restricted pairing agrees with the original partner under `blockLegEquiv`. -/
theorem QuarticDiagram.restrictedPairing_partner_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPairing hB).partner (d.blockLegEquiv hB leg) =
      d.blockLegEquiv hB (d.restrictedPartner B leg) := by
  simpa only [QuarticDiagram.restrictedPairing, QuarticDiagram.restrictedPartner] using
    d.pairing.restrictAlongEquiv_partner (d.legInBlock B)
      (fun i => d.legInBlock_partner_iff i) (d.blockLegEquiv hB) leg

/-- Restrict `d` to the connected-component part `B`. -/
noncomputable def QuarticDiagram.restrictComponent {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : QuarticDiagram Label N B where
  vertexLabel v :=
    d.vertexLabel ((Combinatorics.subsetSubtypeEquiv B (d.componentPartition.le hB)).symm v).1
  pairing := d.restrictedPairing hB

theorem QuarticDiagram.restrictComponent_pairing {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).pairing = d.restrictedPairing hB :=
  rfl

end Common
end SecondQuantization
