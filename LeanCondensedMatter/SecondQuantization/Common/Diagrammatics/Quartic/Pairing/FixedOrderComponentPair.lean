import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentOrder

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

/-- The generic component-pair decomposition specialized to a fixed global vertex order. -/
private noncomputable def QuarticDiagram.fixedOrderComponentPairEquiv
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) :
    (Σ C : d.componentPartition.parts,
      d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) ≃
      (d.pairingInOrder order).NormalizedPair := by
  simpa only [d.assembleVertexOrder_fixedOrderComponentShuffle order] using
    d.componentPairEquiv (d.componentPartition.partOrdersOfOrder order)
      (d.fixedOrderComponentShuffle order)

/-- The connected component containing a normalized pair in a fixed global vertex order. -/
noncomputable def QuarticDiagram.fixedOrderPairComponent
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) : d.componentPartition.parts :=
  ((d.fixedOrderComponentPairEquiv order).symm pr).1

/-- Embed the normalized pairs of one restricted component into the normalized pairs of the global
pairing in the fixed vertex order. -/
noncomputable def QuarticDiagram.fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts) :
    d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C ↪
      (d.pairingInOrder order).NormalizedPair where
  toFun pr := d.fixedOrderComponentPairEquiv order ⟨C, pr⟩
  inj' := by
    intro p q hpq
    have h := (d.fixedOrderComponentPairEquiv order).injective hpq
    cases h
    rfl

@[simp]
private theorem QuarticDiagram.fixedOrderComponentPairEmbedding_apply
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentPartition.partOrdersOfOrder order) C) :
    (d.fixedOrderComponentPairEmbedding order C pr).1 =
      (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.1,
        d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.2) := by
  change (d.fixedOrderComponentPairEquiv order ⟨C, pr⟩).1 = _
  simpa only [QuarticDiagram.fixedOrderComponentPairEquiv,
      d.assembleVertexOrder_fixedOrderComponentShuffle order] using
    d.componentPairEquiv_apply (d.componentPartition.partOrdersOfOrder order)
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
  change
    ((d.fixedOrderComponentPairEquiv order).symm
      (d.fixedOrderComponentPairEquiv order ⟨C, pr⟩)).1 = C
  rw [Equiv.symm_apply_apply]

end Common
end SecondQuantization
