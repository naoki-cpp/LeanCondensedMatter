import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairEquiv

set_option linter.style.header false

/-!
# Fixed-order quartic component pairs

A global quartic vertex order canonically induces component-local orders and a component shuffle.
The existing component-pair equivalence gives the fixed-order normalized-pair embedding by
inclusion of a single component into the dependent sum of all component pairs.

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
  d.vertexGraph.componentPartitionOn.shuffleOfOrder order
    (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order)
    (d.vertexGraph.componentPartitionOn.partOrdersCompatible_partOrdersOfOrder order)

@[simp]
theorem QuarticDiagram.assembleVertexOrder_fixedOrderComponentShuffle
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) :
    d.assembleVertexOrder (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order)
        (d.fixedOrderComponentShuffle order) = order :=
  d.vertexGraph.componentPartitionOn.assembleOrder_shuffleOfOrder order
    (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order)
    (d.vertexGraph.componentPartitionOn.partOrdersCompatible_partOrdersOfOrder order)

/-- The connected component containing the first endpoint of a normalized pair in a fixed global
vertex order. -/
noncomputable def QuarticDiagram.fixedOrderPairComponent
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) : d.vertexGraph.componentPartitionOn.parts :=
  let q := orderedLegToDiagramLeg S order pr.1.1
  ⟨d.vertexGraph.componentBlockOn (vertexOfLeg q), by
    unfold SimpleGraph.componentBlockOn
    exact d.vertexGraph.componentPartitionOn.part_mem.2 (vertexOfLeg q).2⟩

/-- Embed the normalized pairs of one restricted component into the normalized pairs of the
global pairing in the fixed vertex order, through the canonical component-pair equivalence. -/
noncomputable def QuarticDiagram.fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.vertexGraph.componentPartitionOn.parts) :
    d.LocalOrderedPair (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order) C ↪
      (d.pairingInOrder order).NormalizedPair := by
  let orders := d.vertexGraph.componentPartitionOn.partOrdersOfOrder order
  let shuffle := d.fixedOrderComponentShuffle order
  let e := d.componentPairEquiv orders shuffle
  have hpair :
      d.pairingInOrder (d.assembleVertexOrder orders shuffle) =
        d.pairingInOrder order :=
    congrArg (d.pairingInOrder) (d.assembleVertexOrder_fixedOrderComponentShuffle order)
  exact {
    toFun := fun pr =>
      ⟨(e ⟨C, pr⟩).1, by
        rw [← hpair]
        exact (e ⟨C, pr⟩).2⟩
    inj' := by
      intro p q hpq
      have hval : (e ⟨C, p⟩).1 = (e ⟨C, q⟩).1 :=
        congrArg (fun x : (d.pairingInOrder order).NormalizedPair => x.1) hpq
      have hpq' : e ⟨C, p⟩ = e ⟨C, q⟩ :=
        Subtype.ext hval
      have h : (⟨C, p⟩ : Σ B : d.vertexGraph.componentPartitionOn.parts,
          d.LocalOrderedPair orders B) = ⟨C, q⟩ := e.injective hpq'
      cases h
      rfl
  }

private theorem QuarticDiagram.fixedOrderComponentPairEmbedding_apply
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.vertexGraph.componentPartitionOn.parts)
    (pr : d.LocalOrderedPair (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order) C) :
    (d.fixedOrderComponentPairEmbedding order C pr).1 =
      (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.1,
        d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.2) := by
  change
    (d.componentPairEquiv
        (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order)
        (d.fixedOrderComponentShuffle order) ⟨C, pr⟩).1 = _
  exact d.componentPairEquiv_apply
    (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order)
    (d.fixedOrderComponentShuffle order) C pr

/-- The fixed-order component-pair embedding preserves and reflects crossings. -/
theorem QuarticDiagram.fixedOrderComponentPairEmbedding_crosses_iff
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.vertexGraph.componentPartitionOn.parts)
    (p q : d.LocalOrderedPair (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order) C) :
    Crosses (d.fixedOrderComponentPairEmbedding order C p).1
        (d.fixedOrderComponentPairEmbedding order C q).1 ↔
      Crosses p.1 q.1 := by
  rw [d.fixedOrderComponentPairEmbedding_apply order C p,
    d.fixedOrderComponentPairEmbedding_apply order C q]
  exact crosses_map_iff
    (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C)
    (d.componentOrderedLeg_strictMono (d.fixedOrderComponentShuffle order) C)
    p.1.1 p.1.2 q.1.1 q.1.2

/-- A component-local normalized pair remains assigned to that component after embedding into the
fixed global quartic order. -/
theorem QuarticDiagram.fixedOrderPairComponent_fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.vertexGraph.componentPartitionOn.parts)
    (pr : d.LocalOrderedPair (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order) C) :
    d.fixedOrderPairComponent order (d.fixedOrderComponentPairEmbedding order C pr) = C := by
  apply Subtype.ext
  change d.vertexGraph.componentBlockOn
      (vertexOfLeg (orderedLegToDiagramLeg S order
        (d.fixedOrderComponentPairEmbedding order C pr).1.1)) =
    (C : Finset (Fin N))
  unfold SimpleGraph.componentBlockOn
  apply (d.vertexGraph.componentPartitionOn.part_eq_iff_mem C.2).2
  let shuffle := d.fixedOrderComponentShuffle order
  let localLeg := orderedLegToDiagramLeg (C : Finset (Fin N))
    (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order C) pr.1.1
  have hleg := d.orderedLegToDiagramLeg_componentOrderedLeg
    (d.vertexGraph.componentPartitionOn.partOrdersOfOrder order) shuffle C pr.1.1
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
