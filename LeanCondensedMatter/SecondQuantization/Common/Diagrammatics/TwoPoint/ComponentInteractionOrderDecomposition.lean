import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Decomposing two-point interaction orders by full components

The interaction vertices belonging to the full external-plus-vacuum components form a dependent
disjoint union.  A global interaction-vertex order is therefore equivalent to one local order on
each component interaction part together with an order-preserving component shuffle.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel M : Type*} {N : ℕ}

/-- One interaction-vertex order for every full component. -/
abbrev TwoPointDiagram.ComponentInteractionOrders {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :=
  ∀ B : d.componentPartition.parts,
    QuarticVertexOrder (TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))

/-- Identify the sigma type of component-local ordered slots with the ambient interaction vertices. -/
noncomputable def TwoPointDiagram.componentInteractionVertexEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionOrders) :
    (Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) ≃ ↥S :=
  (Equiv.sigmaCongrRight fun B => orders B).trans d.interactionVertexComponentEquiv.symm

/-- Assemble a global interaction-vertex order from local component orders and their shuffle. -/
noncomputable def TwoPointDiagram.assembleInteractionOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionOrders) (shuffle : d.ComponentInteractionShuffle) :
    QuarticVertexOrder S :=
  shuffle.slotEquiv.symm.trans (d.componentInteractionVertexEquiv orders)

@[simp]
theorem TwoPointDiagram.assembleInteractionOrder_symm_componentInteractionVertexEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionOrders) (shuffle : d.ComponentInteractionShuffle)
    (x : Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) :
    (d.assembleInteractionOrder orders shuffle).symm
        (d.componentInteractionVertexEquiv orders x) = shuffle.slotEquiv x := by
  simp [TwoPointDiagram.assembleInteractionOrder]

/-- Compatibility of a local-order family with one global interaction order. -/
noncomputable def TwoPointDiagram.ComponentInteractionOrdersCompatible
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionOrders) : Prop :=
  ∀ B, StrictMono (fun i => order.symm (d.componentInteractionVertexEquiv orders ⟨B, i⟩))

/-- Extract the compatible component shuffle from a global interaction order. -/
noncomputable def TwoPointDiagram.shuffleOfInteractionOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionOrders)
    (h : d.ComponentInteractionOrdersCompatible order orders) : d.ComponentInteractionShuffle where
  slotEquiv := (d.componentInteractionVertexEquiv orders).trans order.symm
  strictMono := h

/-- Locally chosen orders are compatible with the global order assembled from them. -/
theorem TwoPointDiagram.componentInteractionOrdersCompatible_assembleInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionOrders) (shuffle : d.ComponentInteractionShuffle) :
    d.ComponentInteractionOrdersCompatible (d.assembleInteractionOrder orders shuffle) orders := by
  intro B
  simpa [TwoPointDiagram.ComponentInteractionOrdersCompatible,
    TwoPointDiagram.assembleInteractionOrder] using shuffle.strictMono B

/-- Recovering a global interaction order from a compatible local family and its extracted shuffle
returns the original order. -/
@[simp]
theorem TwoPointDiagram.assembleInteractionOrder_shuffleOfInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionOrders)
    (h : d.ComponentInteractionOrdersCompatible order orders) :
    d.assembleInteractionOrder orders (d.shuffleOfInteractionOrder order orders h) = order := by
  ext i
  simp [TwoPointDiagram.assembleInteractionOrder, TwoPointDiagram.shuffleOfInteractionOrder]

/-- Ambient slot occupied by one interaction vertex in a full component. -/
noncomputable def TwoPointDiagram.interactionComponentGlobalSlot {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))) : Fin S.card :=
  order.symm (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)

/-- Distinct interaction vertices of a component occupy distinct global slots. -/
theorem TwoPointDiagram.interactionComponentGlobalSlot_injective {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    Function.Injective (d.interactionComponentGlobalSlot order B) := by
  intro v w h
  have h₁ := order.symm.injective h
  have h₂ := d.interactionVertexComponentEquiv.symm.injective h₁
  cases h₂
  rfl

/-- Finite set of global interaction slots occupied by one component. -/
noncomputable def TwoPointDiagram.interactionComponentGlobalSlots {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) : Finset (Fin S.card) :=
  Finset.univ.image (d.interactionComponentGlobalSlot order B)

@[simp]
theorem TwoPointDiagram.interactionComponentGlobalSlot_mem {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))) :
    d.interactionComponentGlobalSlot order B v ∈ d.interactionComponentGlobalSlots order B :=
  Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩

@[simp]
theorem TwoPointDiagram.card_interactionComponentGlobalSlots {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    (d.interactionComponentGlobalSlots order B).card = d.interactionComponentSize B := by
  rw [TwoPointDiagram.interactionComponentGlobalSlots,
    Finset.card_image_of_injective _ (d.interactionComponentGlobalSlot_injective order B)]
  simp

/-- Component interaction vertices are equivalent to the ambient global slots they occupy. -/
noncomputable def TwoPointDiagram.interactionComponentGlobalSlotEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (order : QuarticVertexOrder S)
    (B : d.componentPartition.parts) :
    ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) ≃
      ↥(d.interactionComponentGlobalSlots order B) :=
  (Equiv.ofInjective (d.interactionComponentGlobalSlot order B)
      (d.interactionComponentGlobalSlot_injective order B)).trans
    (Equiv.setCongr (by
      ext x
      simp [TwoPointDiagram.interactionComponentGlobalSlots]))

/-- Canonical increasing-slot local interaction order induced by a global order. -/
noncomputable def TwoPointDiagram.componentInteractionOrderOfInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    QuarticVertexOrder (TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) :=
  (d.interactionComponentGlobalSlots order B).orderIsoOfFin
      (d.card_interactionComponentGlobalSlots order B) |>.toEquiv.trans
    (d.interactionComponentGlobalSlotEquiv order B).symm

@[simp]
theorem TwoPointDiagram.interactionComponentGlobalSlot_componentInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (i : Fin (d.interactionComponentSize B)) :
    d.interactionComponentGlobalSlot order B
        (d.componentInteractionOrderOfInteractionOrder order B i) =
      ((d.interactionComponentGlobalSlots order B).orderIsoOfFin
        (d.card_interactionComponentGlobalSlots order B) i : Fin S.card) := by
  simp [TwoPointDiagram.componentInteractionOrderOfInteractionOrder]

/-- Canonical family of local interaction orders induced by a global order. -/
noncomputable def TwoPointDiagram.componentInteractionOrdersOfInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) : d.ComponentInteractionOrders :=
  fun B => d.componentInteractionOrderOfInteractionOrder order B

/-- The canonical local order is strictly increasing in ambient slot number. -/
theorem TwoPointDiagram.componentInteractionOrderOfInteractionOrder_strictMono
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    StrictMono (fun i => d.interactionComponentGlobalSlot order B
      (d.componentInteractionOrderOfInteractionOrder order B i)) := by
  intro i j hij
  rw [d.interactionComponentGlobalSlot_componentInteractionOrder,
    d.interactionComponentGlobalSlot_componentInteractionOrder]
  exact ((d.interactionComponentGlobalSlots order B).orderIsoOfFin
    (d.card_interactionComponentGlobalSlots order B)).strictMono hij

/-- The canonical induced local orders are compatible with the global order. -/
theorem TwoPointDiagram.componentInteractionOrdersCompatible_induced
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    d.ComponentInteractionOrdersCompatible order
      (d.componentInteractionOrdersOfInteractionOrder order) := by
  intro B
  simpa [TwoPointDiagram.ComponentInteractionOrdersCompatible,
    TwoPointDiagram.componentInteractionVertexEquiv,
    TwoPointDiagram.componentInteractionOrdersOfInteractionOrder,
    TwoPointDiagram.interactionComponentGlobalSlot] using
    d.componentInteractionOrderOfInteractionOrder_strictMono order B

/-- A compatible local order on one component must be the canonical increasing-slot order. -/
theorem TwoPointDiagram.componentInteractionOrder_eq_of_strictMono
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (localOrder : QuarticVertexOrder
      (TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))))
    (hlocal : StrictMono (fun i => d.interactionComponentGlobalSlot order B (localOrder i))) :
    localOrder = d.componentInteractionOrderOfInteractionOrder order B := by
  apply Equiv.ext
  intro i
  apply d.interactionComponentGlobalSlot_injective order B
  have h := Finset.orderEmbOfFin_unique
    (s := d.interactionComponentGlobalSlots order B)
    (h := d.card_interactionComponentGlobalSlots order B)
    (f := fun i => d.interactionComponentGlobalSlot order B (localOrder i))
    (fun i => d.interactionComponentGlobalSlot_mem order B (localOrder i)) hlocal
  have hi := congrFun h i
  rw [d.interactionComponentGlobalSlot_componentInteractionOrder]
  simpa only [Finset.coe_orderIsoOfFin_apply] using hi

/-- A compatible local-order family is uniquely determined by the global order. -/
theorem TwoPointDiagram.componentInteractionOrders_eq_of_compatible
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionOrders)
    (h : d.ComponentInteractionOrdersCompatible order orders) :
    orders = d.componentInteractionOrdersOfInteractionOrder order := by
  funext B
  apply d.componentInteractionOrder_eq_of_strictMono order B
  simpa [TwoPointDiagram.ComponentInteractionOrdersCompatible,
    TwoPointDiagram.componentInteractionVertexEquiv,
    TwoPointDiagram.interactionComponentGlobalSlot] using h B

/-- A global interaction order is exactly local component orders plus an order-preserving component
shuffle. -/
noncomputable def TwoPointDiagram.componentInteractionOrderDecompositionEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    QuarticVertexOrder S ≃ d.ComponentInteractionOrders × d.ComponentInteractionShuffle where
  toFun order :=
    let orders := d.componentInteractionOrdersOfInteractionOrder order
    ⟨orders, d.shuffleOfInteractionOrder order orders
      (d.componentInteractionOrdersCompatible_induced order)⟩
  invFun x := d.assembleInteractionOrder x.1 x.2
  left_inv order := by
    dsimp
    exact d.assembleInteractionOrder_shuffleOfInteractionOrder order
      (d.componentInteractionOrdersOfInteractionOrder order)
      (d.componentInteractionOrdersCompatible_induced order)
  right_inv x := by
    obtain ⟨orders, shuffle⟩ := x
    dsimp
    have horders :
        d.componentInteractionOrdersOfInteractionOrder
            (d.assembleInteractionOrder orders shuffle) = orders :=
      (d.componentInteractionOrders_eq_of_compatible
        (d.assembleInteractionOrder orders shuffle) orders
        (d.componentInteractionOrdersCompatible_assembleInteractionOrder orders shuffle)).symm
    refine Prod.ext horders ?_
    apply Combinatorics.FamilySlotShuffleTo.ext
    change (d.componentInteractionVertexEquiv
      (d.componentInteractionOrdersOfInteractionOrder
        (d.assembleInteractionOrder orders shuffle))).trans
        (d.assembleInteractionOrder orders shuffle).symm = shuffle.slotEquiv
    have hvertex := congrArg (fun componentOrders => d.componentInteractionVertexEquiv componentOrders) horders
    rw [hvertex]
    ext slot
    simp [TwoPointDiagram.assembleInteractionOrder]

/-- Reindex a finite sum over global interaction orders by local orders and component shuffles. -/
theorem TwoPointDiagram.sum_interactionOrder_eq_sum_componentOrders_shuffle [AddCommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.ComponentInteractionOrders × d.ComponentInteractionShuffle → M) :
    ∑ order : QuarticVertexOrder S,
        F (d.componentInteractionOrderDecompositionEquiv order) =
      ∑ x : d.ComponentInteractionOrders × d.ComponentInteractionShuffle, F x :=
  Equiv.sum_comp d.componentInteractionOrderDecompositionEquiv F

end Common
end SecondQuantization
