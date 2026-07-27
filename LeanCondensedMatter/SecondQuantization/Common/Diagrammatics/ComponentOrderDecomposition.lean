import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrder
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Decomposing global vertex orders into component orders and shuffles

An ambient vertex order canonically induces an order on every connected-component block by sorting
the global slots occupied by that block. These induced local orders are the unique local orders
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

/-- The finite set of ambient slots occupied by component block `B`. -/
noncomputable def QuarticDiagram.componentGlobalSlots {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) : Finset (Fin S.card) :=
  Finset.univ.image (d.componentGlobalSlot order B)

@[simp]
theorem QuarticDiagram.componentGlobalSlot_mem_componentGlobalSlots {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) (v : ↥(B : Finset (Fin N))) :
    d.componentGlobalSlot order B v ∈ d.componentGlobalSlots order B :=
  Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩

/-- A component occupies exactly as many global slots as it has vertices. -/
theorem QuarticDiagram.card_componentGlobalSlots {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    (d.componentGlobalSlots order B).card = (B : Finset (Fin N)).card := by
  rw [QuarticDiagram.componentGlobalSlots,
    Finset.card_image_of_injective _ (d.componentGlobalSlot_injective order B)]
  simp

/-- Component vertices are equivalent to the global slots occupied by that component. -/
noncomputable def QuarticDiagram.componentGlobalSlotEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    ↥(B : Finset (Fin N)) ≃ ↥(d.componentGlobalSlots order B) :=
  Equiv.ofBijective
    (fun v => ⟨d.componentGlobalSlot order B v,
      d.componentGlobalSlot_mem_componentGlobalSlots order B v⟩)
    ⟨by
      intro v w h
      apply d.componentGlobalSlot_injective order B
      exact congrArg Subtype.val h,
    by
      intro slot
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 slot.2
      refine ⟨v, Subtype.ext ?_⟩
      exact hv⟩

@[simp]
theorem QuarticDiagram.componentGlobalSlot_componentGlobalSlotEquiv_symm
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (slot : ↥(d.componentGlobalSlots order B)) :
    d.componentGlobalSlot order B ((d.componentGlobalSlotEquiv order B).symm slot) = slot := by
  have h := congrArg Subtype.val ((d.componentGlobalSlotEquiv order B).apply_symm_apply slot)
  exact h

/-- The canonical order on component `B`, induced by its increasing global slots. -/
noncomputable def QuarticDiagram.componentVertexOrderOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) : QuarticVertexOrder (B : Finset (Fin N)) :=
  (d.componentGlobalSlots order B).orderIsoOfFin
      (d.card_componentGlobalSlots order B) |>.toEquiv.trans
    (d.componentGlobalSlotEquiv order B).symm

@[simp]
theorem QuarticDiagram.componentGlobalSlot_componentVertexOrderOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (i : Fin (B : Finset (Fin N)).card) :
    d.componentGlobalSlot order B (d.componentVertexOrderOfVertexOrder order B i) =
      ((d.componentGlobalSlots order B).orderIsoOfFin
        (d.card_componentGlobalSlots order B) i : Fin S.card) := by
  simp [QuarticDiagram.componentVertexOrderOfVertexOrder]

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
  simpa using
    ((d.componentGlobalSlots order B).orderIsoOfFin
      (d.card_componentGlobalSlots order B)).strictMono

/-- The canonical component-local orders are compatible with the ambient order. -/
theorem QuarticDiagram.componentOrdersCompatible_componentVertexOrdersOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (order : QuarticVertexOrder S) :
    d.ComponentOrdersCompatible order (d.componentVertexOrdersOfVertexOrder order) := by
  intro B
  simpa [QuarticDiagram.ComponentOrdersCompatible, QuarticDiagram.componentVertexEquiv,
    QuarticDiagram.componentVertexOrdersOfVertexOrder, QuarticDiagram.componentGlobalSlot] using
    d.componentVertexOrderOfVertexOrder_strictMono order B

/-- A compatible order on one component must be its canonical increasing-slot order. -/
theorem QuarticDiagram.componentVertexOrder_eq_of_strictMono {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts)
    (localOrder : QuarticVertexOrder (B : Finset (Fin N)))
    (hlocal : StrictMono (fun i => d.componentGlobalSlot order B (localOrder i))) :
    localOrder = d.componentVertexOrderOfVertexOrder order B := by
  apply Equiv.ext
  intro i
  apply d.componentGlobalSlot_injective order B
  have h := Finset.orderEmbOfFin_unique
    (s := d.componentGlobalSlots order B)
    (h := d.card_componentGlobalSlots order B)
    (f := fun i => d.componentGlobalSlot order B (localOrder i))
    (fun i => d.componentGlobalSlot_mem_componentGlobalSlots order B (localOrder i)) hlocal
  have hi := congrFun h i
  simpa [Finset.orderEmbOfFin] using hi

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
    refine Prod.ext horders ?_
    apply QuarticDiagram.ComponentShuffle.ext
    ext slot
    simp [QuarticDiagram.shuffleOfVertexOrder, QuarticDiagram.assembleVertexOrder,
      QuarticDiagram.componentVertexEquiv, horders]

/-- Reindex a finite sum over global vertex orders by component-local orders and shuffles. -/
theorem QuarticDiagram.sum_vertexOrder_eq_sum_componentOrders_shuffle [AddCommMonoid M]
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (F : d.ComponentVertexOrders × d.ComponentShuffle → M) :
    ∑ order : QuarticVertexOrder S, F (d.componentOrderDecompositionEquiv order) =
      ∑ x : d.ComponentVertexOrders × d.ComponentShuffle, F x :=
  Equiv.sum_comp d.componentOrderDecompositionEquiv F

end Common
end SecondQuantization
