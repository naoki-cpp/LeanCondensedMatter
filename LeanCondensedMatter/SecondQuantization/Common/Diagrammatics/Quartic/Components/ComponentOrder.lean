import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentRestriction

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
  d.vertexGraph.componentPartitionOn.PartOrders

/-- An order-preserving interleaving of all component-local slots into the ambient global slots. -/
abbrev QuarticDiagram.ComponentShuffle {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :=
  d.vertexGraph.componentPartitionOn.PartShuffle

/-- Assemble a global vertex order from component-local orders and an order-preserving shuffle. -/
noncomputable def QuarticDiagram.assembleVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) : QuarticVertexOrder S :=
  d.vertexGraph.componentPartitionOn.assembleOrder orders shuffle

end Common
end SecondQuantization
