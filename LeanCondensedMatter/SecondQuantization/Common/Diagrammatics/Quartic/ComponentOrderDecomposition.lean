import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrder

set_option linter.style.header false

/-!
# Decomposing global vertex orders into component orders and shuffles

The underlying finite-partition theorem lives in
`Combinatorics/FinpartitionOrderShuffle.lean`. This module specializes that equivalence to the
connected-component partition of a quartic diagram.
-/

namespace SecondQuantization
namespace Common

variable {Label M : Type*} {N : ℕ}

/-- A global vertex order is equivalent to component-local orders together with an
order-preserving shuffle of their slots. -/
noncomputable def QuarticDiagram.componentOrderDecompositionEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    QuarticVertexOrder S ≃ d.ComponentVertexOrders × d.ComponentShuffle :=
  d.componentPartition.orderDecompositionEquiv

/-- Reindex a finite sum over global vertex orders by component-local orders and shuffles. -/
theorem QuarticDiagram.sum_vertexOrder_eq_sum_componentOrders_shuffle [AddCommMonoid M]
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (F : d.ComponentVertexOrders × d.ComponentShuffle → M) :
    ∑ order : QuarticVertexOrder S, F (d.componentOrderDecompositionEquiv order) =
      ∑ x : d.ComponentVertexOrders × d.ComponentShuffle, F x :=
  Equiv.sum_comp d.componentOrderDecompositionEquiv F

end Common
end SecondQuantization
