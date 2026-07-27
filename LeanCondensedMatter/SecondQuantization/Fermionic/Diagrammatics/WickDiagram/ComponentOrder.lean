import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Ordered

set_option linter.style.header false

/-!
# Fermionic component-local orders and global shuffles

Thin public aliases for the statistics-independent component-order API used by quartic Wick diagrams.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A vertex order on every connected component of a fermionic quartic Wick diagram. -/
abbrev QuarticWickDiagram.ComponentVertexOrders {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :=
  Common.QuarticDiagram.ComponentVertexOrders d

/-- An order-preserving interleaving of component-local slots into global vertex slots. -/
abbrev QuarticWickDiagram.ComponentShuffle {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :=
  Common.QuarticDiagram.ComponentShuffle d

/-- Identify the disjoint union of component-local slots with the ambient vertex set. -/
noncomputable abbrev QuarticWickDiagram.componentVertexEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders) :
    (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) ≃ ↥S :=
  Common.QuarticDiagram.componentVertexEquiv d orders

/-- Assemble a global fermionic vertex order from local component orders and a shuffle. -/
noncomputable abbrev QuarticWickDiagram.assembleVertexOrder {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) : QuarticVertexOrder S :=
  Common.QuarticDiagram.assembleVertexOrder d orders shuffle

/-- Compatibility of component-local orders with a global fermionic vertex order. -/
noncomputable abbrev QuarticWickDiagram.ComponentOrdersCompatible {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) : Prop :=
  Common.QuarticDiagram.ComponentOrdersCompatible d order orders

/-- Extract the component shuffle determined by a compatible global order. -/
noncomputable abbrev QuarticWickDiagram.shuffleOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.ComponentShuffle :=
  Common.QuarticDiagram.shuffleOfVertexOrder d order orders h

/-- Component-local orders are compatible with the global order assembled from them. -/
theorem QuarticWickDiagram.componentOrdersCompatible_assembleVertexOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    d.ComponentOrdersCompatible (d.assembleVertexOrder orders shuffle) orders :=
  Common.QuarticDiagram.componentOrdersCompatible_assembleVertexOrder d orders shuffle

/-- Extracting the shuffle from an assembled order returns the original shuffle. -/
@[simp]
theorem QuarticWickDiagram.shuffleOfVertexOrder_assembleVertexOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    d.shuffleOfVertexOrder (d.assembleVertexOrder orders shuffle) orders
      (d.componentOrdersCompatible_assembleVertexOrder orders shuffle) = shuffle :=
  Common.QuarticDiagram.shuffleOfVertexOrder_assembleVertexOrder d orders shuffle

/-- Assembling from a compatible global order and its extracted shuffle is identity. -/
@[simp]
theorem QuarticWickDiagram.assembleVertexOrder_shuffleOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.assembleVertexOrder orders (d.shuffleOfVertexOrder order orders h) = order :=
  Common.QuarticDiagram.assembleVertexOrder_shuffleOfVertexOrder d order orders h

end SecondQuantization
