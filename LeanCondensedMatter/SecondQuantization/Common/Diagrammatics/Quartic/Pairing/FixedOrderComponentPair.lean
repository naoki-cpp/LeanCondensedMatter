import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairEquiv

set_option linter.style.header false

/-!
# Fixed-order quartic component pairs

A global quartic vertex order canonically induces component-local orders and a component shuffle.
The generic component-pair equivalence then classifies global normalized pairs by component and
embeds each component fiber into the fixed-order global pairing.

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
  d.componentPartition.assembleOrder_shuffleOfOrder order
    (d.componentPartition.partOrdersOfOrder order)
    (d.componentPartition.partOrdersCompatible_partOrdersOfOrder order)

private theorem Pairing.normalizedPair_cast_val {n : ℕ} {p q : Pairing n}
    (h : p = q) (pr : p.NormalizedPair) :
    (Equiv.cast (by rw [h]) pr : q.NormalizedPair).1 = pr.1 := by
  subst q
  rfl

/-- The connected component containing the first endpoint of a normalized pair in a fixed global
vertex order. -/
noncomputable def QuarticDiagram.fixedOrderPairComponent
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) : d.componentPartition.parts :=
  let q := orderedLegToDiagramLeg S order pr.1.1
  ⟨d.componentBlock (vertexOfLeg q), by
    unfold QuarticDiagram.componentBlock
    exact d.componentPartition.part_mem.2 (vertexOfLeg q).2⟩

/-- Embed the normalized pairs of one restricted component into the normalized pairs of the global
pairing in the fixed vertex order. -/
noncomputable def QuarticDiagram.fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts) :
    d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C ↪
      (d.pairingInOrder order).NormalizedPair where
  toFun pr :=
    Equiv.cast (by
      rw [d.assembleVertexOrder_fixedOrderComponentShuffle order])
      (d.componentPairEquiv (d.componentPartition.partOrdersOfOrder order)
        (d.fixedOrderComponentShuffle order) ⟨C, pr⟩)
  inj' := by
    intro p q hpq
    have h := (Equiv.cast (by
      rw [d.assembleVertexOrder_fixedOrderComponentShuffle order])).injective hpq
    have hs := (d.componentPairEquiv (d.componentPartition.partOrdersOfOrder order)
      (d.fixedOrderComponentShuffle order)).injective h
    cases hs
    rfl

private theorem QuarticDiagram.fixedOrderComponentPairEmbedding_apply
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    (d.fixedOrderComponentPairEmbedding order C pr).1 =
      (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.1,
        d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.2) := by
  let hpair :
      d.pairingInOrder
          (d.assembleVertexOrder (d.componentPartition.partOrdersOfOrder order)
            (d.fixedOrderComponentShuffle order)) =
        d.pairingInOrder order :=
    congrArg d.pairingInOrder
      (d.assembleVertexOrder_fixedOrderComponentShuffle order)
  change
    ((Equiv.cast
      (congrArg (fun p => p.NormalizedPair) hpair)
      (d.componentPairEquiv (d.componentPartition.partOrdersOfOrder order)
        (d.fixedOrderComponentShuffle order) ⟨C, pr⟩) :
      (d.pairingInOrder order).NormalizedPair)).1 = _
  rw [Pairing.normalizedPair_cast_val hpair]
  exact d.componentPairEquiv_apply (d.componentPartition.partOrdersOfOrder order)
    (d.fixedOrderComponentShuffle order) C pr

/-- The fixed-order component-pair embedding preserves and reflects crossings. -/
theorem QuarticDiagram.fixedOrderComponentPairEmbedding_crosses_iff
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (p q : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    Crosses (d.fixedOrderComponentPairEmbedding order C p).1
        (d.fixedOrderComponentPairEmbedding order C q).1 ↔
      Crosses p.1 q.1 := by
  rw [d.fixedOrderComponentPairEmbedding_apply, d.fixedOrderComponentPairEmbedding_apply]
  exact crosses_map_iff
    (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C)
    (d.componentOrderedLeg_strictMono (d.fixedOrderComponentShuffle order) C)
    p.1.1 p.1.2 q.1.1 q.1.2

/-- A component-local normalized pair remains assigned to that component after embedding into the
fixed global quartic order. -/
theorem QuarticDiagram.fixedOrderPairComponent_fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    d.fixedOrderPairComponent order (d.fixedOrderComponentPairEmbedding order C pr) = C := by
  apply Subtype.ext
  change d.componentBlock
      (vertexOfLeg (orderedLegToDiagramLeg S order
        (d.fixedOrderComponentPairEmbedding order C pr).1.1)) =
    (C : Finset (Fin N))
  unfold QuarticDiagram.componentBlock
  apply (d.componentPartition.part_eq_iff_mem C.2).2
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
