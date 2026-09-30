import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentRestriction

set_option linter.style.header false

/-!
# Component-local vertex orders and global shuffles

The finite-partition order/shuffle combinatorics is owned by
`Combinatorics/FinpartitionOrderShuffle.lean`. This module provides the quartic-diagram-facing names
obtained by applying that generic API to the diagram's connected-component partition, including the
canonical decomposition of a global order into component-local orders and a shuffle.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- A vertex order on every connected-component block of `d`. -/
abbrev QuarticDiagram.ComponentVertexOrders {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :=
  d.vertexGraph.componentPartitionOn.PartOrders

/-- An order-preserving interleaving of all component-local slots into the ambient global slots. -/
abbrev QuarticDiagram.ComponentShuffle {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :=
  d.vertexGraph.componentPartitionOn.PartShuffle

/-- The disjoint union of component-local slots, identified with the ambient vertex set using the
chosen local order on every component. -/
noncomputable def QuarticDiagram.componentVertexEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders) :
    (Σ B : d.vertexGraph.componentPartitionOn.parts, Fin (B : Finset (Fin N)).card) ≃ ↥S :=
  (Equiv.sigmaCongrRight fun B => orders B).trans d.vertexGraph.componentPartitionOn.equivSigmaParts.symm

/-- Assemble a global vertex order from component-local orders and an order-preserving shuffle. -/
noncomputable def QuarticDiagram.assembleVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) : QuarticVertexOrder S :=
  shuffle.slotEquiv.symm.trans (d.componentVertexEquiv orders)

/-- A family of component-local orders is compatible with a global order when each component appears
in the global slots in precisely that local order. -/
noncomputable def QuarticDiagram.ComponentOrdersCompatible {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) : Prop :=
  d.vertexGraph.componentPartitionOn.PartOrdersCompatible order orders

/-- Read off the unique component shuffle from a global order and compatible component-local orders. -/
noncomputable def QuarticDiagram.shuffleOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.ComponentShuffle :=
  d.vertexGraph.componentPartitionOn.shuffleOfOrder order orders h

/-- A global vertex order is equivalent to component-local orders together with an
order-preserving shuffle of their slots. -/
noncomputable def QuarticDiagram.componentOrderDecompositionEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    QuarticVertexOrder S ≃ d.ComponentVertexOrders × d.ComponentShuffle :=
  d.vertexGraph.componentPartitionOn.orderDecompositionEquiv

/-- Diagram-facing specialization of the generic finite-partition order/shuffle sum theorem.
A global vertex-order sum factors into component-local order sums once the fixed-local-orders
shuffle fiber is known to be a common scalar times the product of local weights. -/
theorem QuarticDiagram.sum_vertexOrder_eq_mul_prod_sum_componentOrders
    {R : Type*} [CommSemiring R] {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S)
    (globalWeight : QuarticVertexOrder S → R)
    (localWeight :
      ∀ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticVertexOrder (B : Finset (Fin N)) → R)
    (c : R)
    (hshuffle : ∀ orders : d.ComponentVertexOrders,
      (∑ shuffle : d.ComponentShuffle,
        globalWeight (d.assembleVertexOrder orders shuffle)) =
        c * ∏ B : d.vertexGraph.componentPartitionOn.parts,
          localWeight B (orders B)) :
    (∑ order : QuarticVertexOrder S, globalWeight order) =
      c * ∏ B : d.vertexGraph.componentPartitionOn.parts,
        ∑ order : QuarticVertexOrder (B : Finset (Fin N)),
          localWeight B order := by
  classical
  exact Finpartition.sum_order_eq_mul_prod_sum_partOrders
    d.vertexGraph.componentPartitionOn globalWeight localWeight c hshuffle

end Common
end SecondQuantization
