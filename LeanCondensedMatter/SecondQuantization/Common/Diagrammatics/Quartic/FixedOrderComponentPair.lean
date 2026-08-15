import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderDecomposition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Embedding

set_option linter.style.header false

/-!
# Fixed-order quartic component pairs

A global quartic vertex order canonically induces component-local orders and a component shuffle.
This module embeds each restricted component's normalized pairs into the global fixed-order pairing
and records preservation of component identity and crossing geometry.

Everything here is independent of particle statistics and of the vertex-label type.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*}

/-- The canonical component shuffle induced by one fixed quartic vertex order. -/
noncomputable def QuarticDiagram.fixedOrderComponentShuffle
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) : d.ComponentShuffle :=
  d.shuffleOfVertexOrder order (d.componentPartition.partOrdersOfOrder order)
    (d.componentPartition.partOrdersCompatible_partOrdersOfOrder order)

@[simp]
theorem QuarticDiagram.assembleVertexOrder_fixedOrderComponentShuffle
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) :
    d.assembleVertexOrder (d.componentPartition.partOrdersOfOrder order)
        (d.fixedOrderComponentShuffle order) = order :=
  d.assembleVertexOrder_shuffleOfVertexOrder order
    (d.componentPartition.partOrdersOfOrder order)
    (d.componentPartition.partOrdersCompatible_partOrdersOfOrder order)

/-- The connected component containing the first endpoint of a normalized pair in a fixed global
vertex order. -/
noncomputable def QuarticDiagram.fixedOrderPairComponent
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) : d.componentPartition.parts :=
  let q := orderedLegToDiagramLeg S order pr.1.1
  ⟨d.componentBlock (vertexOfLeg q),
    d.componentBlock_mem_componentPartition (vertexOfLeg q)⟩

@[simp]
theorem QuarticDiagram.fixedOrderPairComponent_val
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) :
    (d.fixedOrderPairComponent order pr : Finset (Fin N)) =
      d.componentBlock (vertexOfLeg (orderedLegToDiagramLeg S order pr.1.1)) :=
  rfl

/-- In a fixed global vertex order, the component ordered-leg embedding intertwines the restricted
and global pairing partner maps. -/
theorem QuarticDiagram.pairingInOrder_partner_fixedOrderComponentOrderedLeg
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (p : Fin (2 * (2 * (C : Finset (Fin N)).card))) :
    (d.pairingInOrder order).partner
        (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C p) =
      d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C
        (((d.restrictComponent C.2).pairingInOrder
          (d.componentPartition.partOrdersOfOrder order C)).partner p) := by
  simpa only [d.assembleVertexOrder_fixedOrderComponentShuffle order] using
    d.pairingInOrder_partner_componentOrderedLeg
      (d.componentPartition.partOrdersOfOrder order)
      (d.fixedOrderComponentShuffle order) C p

/-- Embed the normalized pairs of one restricted component into the normalized pairs of the global
pairing in the fixed vertex order. -/
noncomputable def QuarticDiagram.fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts) :
    d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C ↪
      (d.pairingInOrder order).NormalizedPair :=
  ((d.restrictComponent C.2).pairingInOrder
      (d.componentPartition.partOrdersOfOrder order C)).normalizedPairEmbedding
    (d.pairingInOrder order)
    (d.componentOrderedLegOrderEmbedding (d.fixedOrderComponentShuffle order) C)
    (d.pairingInOrder_partner_fixedOrderComponentOrderedLeg order C)

@[simp]
theorem QuarticDiagram.fixedOrderComponentPairEmbedding_apply
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    (d.fixedOrderComponentPairEmbedding order C pr).1 =
      (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.1,
        d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.2) :=
  rfl

/-- The fixed-order component-pair embedding preserves and reflects crossings. -/
theorem QuarticDiagram.fixedOrderComponentPairEmbedding_crosses_iff
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (p q : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    Crosses (d.fixedOrderComponentPairEmbedding order C p).1
        (d.fixedOrderComponentPairEmbedding order C q).1 ↔
      Crosses p.1 q.1 := by
  simpa only [QuarticDiagram.fixedOrderComponentPairEmbedding] using
    ((d.restrictComponent C.2).pairingInOrder
      (d.componentPartition.partOrdersOfOrder order C)).normalizedPairEmbedding_crosses_iff
      (d.pairingInOrder order)
      (d.componentOrderedLegOrderEmbedding (d.fixedOrderComponentShuffle order) C)
      (d.pairingInOrder_partner_fixedOrderComponentOrderedLeg order C) p q

/-- A component-local normalized pair remains assigned to that component after embedding into the
fixed global quartic order. -/
theorem QuarticDiagram.fixedOrderPairComponent_fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    d.fixedOrderPairComponent order (d.fixedOrderComponentPairEmbedding order C pr) = C := by
  apply Subtype.ext
  apply (d.componentBlock_eq_iff_mem C.2 _).2
  let shuffle := d.fixedOrderComponentShuffle order
  let localLeg := orderedLegToDiagramLeg (C : Finset (Fin N))
    (d.componentPartition.partOrdersOfOrder order C) pr.1.1
  have hleg := d.orderedLegToDiagramLeg_componentOrderedLeg
    (d.componentPartition.partOrdersOfOrder order) shuffle C pr.1.1
  rw [d.assembleVertexOrder_fixedOrderComponentShuffle order] at hleg
  change ((vertexOfLeg
      (orderedLegToDiagramLeg S order
        (d.fixedOrderComponentPairEmbedding order C pr).1.1) : ↥S) : Fin N) ∈
    (C : Finset (Fin N))
  rw [d.fixedOrderComponentPairEmbedding_apply, hleg]
  have hv := d.vertexOfLeg_componentDiagramLeg_val C localLeg
  rw [hv]
  exact (vertexOfLeg localLeg).2

end Common
end SecondQuantization
