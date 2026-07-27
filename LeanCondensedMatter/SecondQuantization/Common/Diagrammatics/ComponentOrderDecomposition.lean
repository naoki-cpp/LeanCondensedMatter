import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrder
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Decomposing global vertex orders into component orders and shuffles

An ambient vertex order canonically induces an order on every connected-component block by sorting
that block according to its ambient slot. These induced local orders are the unique local orders
compatible with the ambient order. Consequently, global vertex orders are equivalent to pairs of
component-local orders and order-preserving component shuffles.
-/

namespace SecondQuantization
namespace Common

variable {Label M : Type*} {N : ℕ}

/-- The ambient slot occupied by a vertex of component block `B`. -/
noncomputable def QuarticDiagram.componentGlobalSlot {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) (v : ↥(B : Finset (Fin N))) : Fin S.card :=
  order.symm (d.componentPartition.equivSigmaParts.symm ⟨B, v⟩)

/-- Distinct vertices of one component occupy distinct ambient slots. -/
theorem QuarticDiagram.componentGlobalSlot_injective {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    Function.Injective (d.componentGlobalSlot order B) := by
  intro v w h
  have h₁ := order.symm.injective h
  have h₂ := d.componentPartition.equivSigmaParts.symm.injective h₁
  cases h₂
  rfl

/-- The linear order on one component obtained by pulling back the ambient slot order. -/
@[reducible]
noncomputable def QuarticDiagram.componentVertexLinearOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) : LinearOrder ↥(B : Finset (Fin N)) :=
  LinearOrder.lift' (d.componentGlobalSlot order B)
    (d.componentGlobalSlot_injective order B)

/-- The canonical order on component `B`, induced by an ambient vertex order. -/
noncomputable def QuarticDiagram.componentVertexOrderOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) : QuarticVertexOrder (B : Finset (Fin N)) := by
  letI := d.componentVertexLinearOrder order B
  let e := (Finset.univ : Finset ↥(B : Finset (Fin N))).orderIsoOfFin
    (k := (B : Finset (Fin N)).card) (by simp)
  exact
    { toFun := fun i => (e i).1
      invFun := fun v => e.symm ⟨v, Finset.mem_univ v⟩
      left_inv := fun i => e.symm_apply_apply i
      right_inv := fun v => congrArg Subtype.val (e.apply_symm_apply ⟨v, Finset.mem_univ v⟩) }

/-- The canonical family of component-local orders induced by an ambient order. -/
noncomputable def QuarticDiagram.componentVertexOrdersOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S) :
    d.ComponentVertexOrders :=
  fun B => d.componentVertexOrderOfVertexOrder order B

/-- The canonical local order of each component is strictly increasing in ambient slot number. -/
theorem QuarticDiagram.componentVertexOrderOfVertexOrder_strictMono {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    StrictMono (fun i => d.componentGlobalSlot order B
      (d.componentVertexOrderOfVertexOrder order B i)) := by
  letI := d.componentVertexLinearOrder order B
  let e := (Finset.univ : Finset ↥(B : Finset (Fin N))).orderIsoOfFin
    (k := (B : Finset (Fin N)).card) (by simp)
  simpa [QuarticDiagram.componentVertexOrderOfVertexOrder] using
    (e.strictMono : StrictMono fun i => (e i).1)

/-- The canonical component-local orders are compatible with the ambient order. -/
theorem QuarticDiagram.componentOrdersCompatible_componentVertexOrdersOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) :
    d.ComponentOrdersCompatible order (d.componentVertexOrdersOfVertexOrder order) := by
  intro B
  simpa [QuarticDiagram.ComponentOrdersCompatible, QuarticDiagram.componentVertexEquiv,
    QuarticDiagram.componentVertexOrdersOfVertexOrder, QuarticDiagram.componentGlobalSlot] using
    d.componentVertexOrderOfVertexOrder_strictMono order B

/-- A compatible order on one component must be its canonical ambient-slot order. -/
theorem QuarticDiagram.componentVertexOrder_eq_of_strictMono {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts)
    (localOrder : QuarticVertexOrder (B : Finset (Fin N)))
    (hlocal : StrictMono (fun i => d.componentGlobalSlot order B (localOrder i))) :
    localOrder = d.componentVertexOrderOfVertexOrder order B := by
  letI := d.componentVertexLinearOrder order B
  apply Equiv.ext
  funext i
  have hmono : StrictMono (fun i => localOrder i) := by
    intro a b hab
    change d.componentGlobalSlot order B (localOrder a) <
      d.componentGlobalSlot order B (localOrder b)
    exact hlocal hab
  have h := Finset.orderEmbOfFin_unique
    (s := (Finset.univ : Finset ↥(B : Finset (Fin N))))
    (k := (B : Finset (Fin N)).card) (by simp)
    (f := fun i => localOrder i) (fun _ => Finset.mem_univ _) hmono
  have hi := congrFun h i
  simpa [QuarticDiagram.componentVertexOrderOfVertexOrder] using hi

/-- A compatible family of component-local orders is uniquely determined by the ambient order. -/
theorem QuarticDiagram.componentVertexOrders_eq_of_compatible {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    orders = d.componentVertexOrdersOfVertexOrder order := by
  funext B
  apply d.componentVertexOrder_eq_of_strictMono order B
  simpa [QuarticDiagram.ComponentOrdersCompatible, QuarticDiagram.componentVertexEquiv,
    QuarticDiagram.componentGlobalSlot] using h B

/-- Component shuffles form a finite type. -/
noncomputable instance QuarticDiagram.ComponentShuffle.instFintype {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : Fintype d.ComponentShuffle :=
  Fintype.ofInjective (fun shuffle : d.ComponentShuffle => shuffle.slotEquiv)
    (fun _ _ h => QuarticDiagram.ComponentShuffle.ext h)

/-- A global vertex order is equivalent to component-local orders together with an
order-preserving shuffle of their slots. -/
noncomputable def QuarticDiagram.componentOrderDecompositionEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    QuarticVertexOrder S ≃ d.ComponentVertexOrders × d.ComponentShuffle where
  toFun order :=
    let orders := d.componentVertexOrdersOfVertexOrder order
    ⟨orders, d.shuffleOfVertexOrder order orders
      (d.componentOrdersCompatible_componentVertexOrdersOfVertexOrder order)⟩
  invFun x := d.assembleVertexOrder x.1 x.2
  left_inv order := by
    dsimp
    exact d.assembleVertexOrder_shuffleOfVertexOrder order
      (d.componentVertexOrdersOfVertexOrder order)
      (d.componentOrdersCompatible_componentVertexOrdersOfVertexOrder order)
  right_inv x := by
    obtain ⟨orders, shuffle⟩ := x
    dsimp
    have horders :
        d.componentVertexOrdersOfVertexOrder (d.assembleVertexOrder orders shuffle) = orders :=
      (d.componentVertexOrders_eq_of_compatible
        (d.assembleVertexOrder orders shuffle) orders
        (d.componentOrdersCompatible_assembleVertexOrder orders shuffle)).symm
    apply Prod.ext
    · exact horders
    · cases horders
      simpa using d.shuffleOfVertexOrder_assembleVertexOrder orders shuffle

/-- Reindex a finite sum over global vertex orders by component-local orders and shuffles. -/
theorem QuarticDiagram.sum_vertexOrder_eq_sum_componentOrders_shuffle [AddCommMonoid M]
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (F : d.ComponentVertexOrders × d.ComponentShuffle → M) :
    ∑ order : QuarticVertexOrder S, F (d.componentOrderDecompositionEquiv order) =
      ∑ x : d.ComponentVertexOrders × d.ComponentShuffle, F x :=
  Equiv.sum_comp d.componentOrderDecompositionEquiv F

end Common
end SecondQuantization
