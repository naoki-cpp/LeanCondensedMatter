import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentRestriction

set_option linter.style.header false

/-!
# Component-local vertex orders and global shuffles

The finite-partition order/shuffle combinatorics is owned by
`Combinatorics/FinpartitionOrderShuffle.lean`. This module provides the quartic-diagram-facing names
obtained by applying that generic API to the diagram's connected-component partition.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- A vertex order on every connected-component block of `d`. -/
abbrev QuarticDiagram.ComponentVertexOrders {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :=
  d.componentPartition.PartOrders

/-- An order-preserving interleaving of all component-local slots into the ambient global slots. -/
abbrev QuarticDiagram.ComponentShuffle {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :=
  d.componentPartition.PartShuffle

/-- The disjoint union of component-local slots, identified with the ambient vertex set using the
chosen local order on every component. -/
noncomputable def QuarticDiagram.componentVertexEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders) :
    (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) ≃ ↥S :=
  d.componentPartition.partEquiv orders

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
  d.componentPartition.PartOrdersCompatible order orders

/-- Read off the unique component shuffle from a global order and compatible component-local orders. -/
noncomputable def QuarticDiagram.shuffleOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.ComponentShuffle :=
  d.componentPartition.shuffleOfOrder order orders h

/-- Reassembling a global order from its compatible component-local orders and extracted shuffle is
identity. -/
@[simp]
theorem QuarticDiagram.assembleVertexOrder_shuffleOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.assembleVertexOrder orders (d.shuffleOfVertexOrder order orders h) = order :=
  d.componentPartition.assembleOrder_shuffleOfOrder order orders h

end Common
end SecondQuantization
