import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrderDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrder

set_option linter.style.header false

/-!
# Fermionic global-order decomposition into component orders and shuffles

Thin public aliases for the statistics-independent order-decomposition equivalence used by quartic
Wick diagrams.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode M : Type*} {N : ℕ}

/-- The ambient slot occupied by a vertex of one fermionic Wick-diagram component. -/
noncomputable abbrev QuarticWickDiagram.componentGlobalSlot {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) (v : ↥(B : Finset (Fin N))) : Fin S.card :=
  Common.QuarticDiagram.componentGlobalSlot d order B v

/-- Canonical component-local orders induced by a global fermionic vertex order. -/
noncomputable abbrev QuarticWickDiagram.componentVertexOrdersOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : QuarticVertexOrder S) : d.ComponentVertexOrders :=
  Common.QuarticDiagram.componentVertexOrdersOfVertexOrder d order

/-- The canonical fermionic component orders are compatible with the global order. -/
theorem QuarticWickDiagram.componentOrdersCompatible_componentVertexOrdersOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : QuarticVertexOrder S) :
    d.ComponentOrdersCompatible order (d.componentVertexOrdersOfVertexOrder order) :=
  Common.QuarticDiagram.componentOrdersCompatible_componentVertexOrdersOfVertexOrder d order

/-- Compatible component-local orders are uniquely determined by the global order. -/
theorem QuarticWickDiagram.componentVertexOrders_eq_of_compatible {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    orders = d.componentVertexOrdersOfVertexOrder order :=
  Common.QuarticDiagram.componentVertexOrders_eq_of_compatible d order orders h

/-- Fermionic global vertex orders are equivalent to component-local orders and shuffles. -/
noncomputable abbrev QuarticWickDiagram.componentOrderDecompositionEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) :
    QuarticVertexOrder S ≃ d.ComponentVertexOrders × d.ComponentShuffle :=
  Common.QuarticDiagram.componentOrderDecompositionEquiv d

/-- Reindex a finite sum over fermionic global vertex orders by local orders and shuffles. -/
theorem QuarticWickDiagram.sum_vertexOrder_eq_sum_componentOrders_shuffle [AddCommMonoid M]
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (F : d.ComponentVertexOrders × d.ComponentShuffle → M) :
    ∑ order : QuarticVertexOrder S, F (d.componentOrderDecompositionEquiv order) =
      ∑ x : d.ComponentVertexOrders × d.ComponentShuffle, F x :=
  Common.QuarticDiagram.sum_vertexOrder_eq_sum_componentOrders_shuffle d F

end Fermionic
end SecondQuantization
