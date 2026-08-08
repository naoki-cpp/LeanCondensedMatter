import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordered
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false

/-!
# Component decomposition of two-point interaction orders

A global order of the interaction vertices of a two-point diagram is exactly a family of local
orders, one on the interaction part of every full component, together with one order-preserving
component shuffle.  This is the finite combinatorial bridge used by the external-leg LCT; it does
not introduce any diagram quotient or orbit/stabilizer layer.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {M : Type*}

noncomputable section

/-- An interaction-vertex order on every full component of a two-point diagram. -/
abbrev TwoPointDiagram.ComponentInteractionVertexOrders {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :=
  ∀ B : d.componentPartition.parts,
    QuarticVertexOrder (TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))

/-- The disjoint family of component-local ordered slots identified with the ambient interaction
vertices. -/
def TwoPointDiagram.componentInteractionVertexEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders) :
    (Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) ≃ ↥S :=
  (Equiv.sigmaCongrRight fun B => orders B).trans d.interactionVertexComponentEquiv.symm

/-- Assemble an ambient interaction-vertex order from component-local orders and a shuffle. -/
def TwoPointDiagram.assembleInteractionVertexOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders)
    (shuffle : d.ComponentInteractionShuffle) : QuarticVertexOrder S :=
  shuffle.slotEquiv.symm.trans (d.componentInteractionVertexEquiv orders)

@[simp]
theorem TwoPointDiagram.assembleInteractionVertexOrder_apply {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders)
    (shuffle : d.ComponentInteractionShuffle) (i : Fin S.card) :
    d.assembleInteractionVertexOrder orders shuffle i =
      d.componentInteractionVertexEquiv orders (shuffle.slotEquiv.symm i) :=
  rfl

@[simp]
theorem TwoPointDiagram.assembleInteractionVertexOrder_symm_componentInteractionVertexEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders)
    (shuffle : d.ComponentInteractionShuffle)
    (x : Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) :
    (d.assembleInteractionVertexOrder orders shuffle).symm
        (d.componentInteractionVertexEquiv orders x) =
      shuffle.slotEquiv x := by
  simp [TwoPointDiagram.assembleInteractionVertexOrder]

/-- A family of component-local interaction orders is compatible with a global order when every
component occurs in that local order. -/
def TwoPointDiagram.ComponentInteractionOrdersCompatible {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionVertexOrders) : Prop :=
  ∀ B, StrictMono (fun i => order.symm (d.componentInteractionVertexEquiv orders ⟨B, i⟩))

/-- Read off the component shuffle from a global interaction order and compatible local orders. -/
def TwoPointDiagram.interactionShuffleOfVertexOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionVertexOrders)
    (h : d.ComponentInteractionOrdersCompatible order orders) :
    d.ComponentInteractionShuffle where
  slotEquiv := (d.componentInteractionVertexEquiv orders).trans order.symm
  strictMono := h

/-- Local orders used to assemble a global order are compatible with it. -/
theorem TwoPointDiagram.componentInteractionOrdersCompatible_assemble
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders)
    (shuffle : d.ComponentInteractionShuffle) :
    d.ComponentInteractionOrdersCompatible
      (d.assembleInteractionVertexOrder orders shuffle) orders := by
  intro B
  simpa [TwoPointDiagram.ComponentInteractionOrdersCompatible,
    TwoPointDiagram.assembleInteractionVertexOrder] using shuffle.strictMono B

@[simp]
theorem TwoPointDiagram.interactionShuffleOfVertexOrder_assemble
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders)
    (shuffle : d.ComponentInteractionShuffle) :
    d.interactionShuffleOfVertexOrder (d.assembleInteractionVertexOrder orders shuffle) orders
      (d.componentInteractionOrdersCompatible_assemble orders shuffle) = shuffle := by
  apply Combinatorics.FamilySlotShuffleTo.ext
  ext x
  simp [TwoPointDiagram.interactionShuffleOfVertexOrder,
    TwoPointDiagram.assembleInteractionVertexOrder]

@[simp]
theorem TwoPointDiagram.assembleInteractionVertexOrder_interactionShuffleOfVertexOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionVertexOrders)
    (h : d.ComponentInteractionOrdersCompatible order orders) :
    d.assembleInteractionVertexOrder orders
      (d.interactionShuffleOfVertexOrder order orders h) = order := by
  ext i
  simp [TwoPointDiagram.assembleInteractionVertexOrder,
    TwoPointDiagram.interactionShuffleOfVertexOrder]

/-- Ambient slot occupied by one actual interaction vertex of a component. -/
def TwoPointDiagram.componentInteractionGlobalSlot {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))) : Fin S.card :=
  order.symm (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)

/-- Distinct interaction vertices of one component occupy distinct global slots. -/
theorem TwoPointDiagram.componentInteractionGlobalSlot_injective {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    Function.Injective (d.componentInteractionGlobalSlot order B) := by
  intro v w h
  have h₁ := order.symm.injective h
  have h₂ := d.interactionVertexComponentEquiv.symm.injective h₁
  cases h₂
  rfl

/-- Global slots occupied by the interaction vertices of one full component. -/
def TwoPointDiagram.componentInteractionGlobalSlots {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) : Finset (Fin S.card) :=
  Finset.univ.image (d.componentInteractionGlobalSlot order B)

@[simp]
theorem TwoPointDiagram.componentInteractionGlobalSlot_mem {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))) :
    d.componentInteractionGlobalSlot order B v ∈ d.componentInteractionGlobalSlots order B :=
  Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩

/-- A component occupies as many interaction slots as its interaction part contains vertices. -/
theorem TwoPointDiagram.card_componentInteractionGlobalSlots {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    (d.componentInteractionGlobalSlots order B).card = d.interactionComponentSize B := by
  rw [TwoPointDiagram.componentInteractionGlobalSlots,
    Finset.card_image_of_injective _ (d.componentInteractionGlobalSlot_injective order B)]
  simp

/-- Actual component interaction vertices are equivalent to their occupied ambient slots. -/
def TwoPointDiagram.componentInteractionGlobalSlotEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) ≃
      ↥(d.componentInteractionGlobalSlots order B) :=
  (Equiv.ofInjective (d.componentInteractionGlobalSlot order B)
      (d.componentInteractionGlobalSlot_injective order B)).trans
    (Equiv.setCongr (by
      ext x
      simp [TwoPointDiagram.componentInteractionGlobalSlots]))

@[simp]
theorem TwoPointDiagram.componentInteractionGlobalSlot_componentInteractionGlobalSlotEquiv_symm
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (slot : ↥(d.componentInteractionGlobalSlots order B)) :
    d.componentInteractionGlobalSlot order B
        ((d.componentInteractionGlobalSlotEquiv order B).symm slot) = slot := by
  have h := congrArg Subtype.val
    ((d.componentInteractionGlobalSlotEquiv order B).apply_symm_apply slot)
  exact h

/-- Canonical local interaction order induced by increasing occupied ambient slots. -/
def TwoPointDiagram.componentInteractionVertexOrderOfVertexOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    QuarticVertexOrder (TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S))) :=
  (d.componentInteractionGlobalSlots order B).orderIsoOfFin
      (d.card_componentInteractionGlobalSlots order B) |>.toEquiv.trans
    (d.componentInteractionGlobalSlotEquiv order B).symm

@[simp]
theorem TwoPointDiagram.componentInteractionGlobalSlot_componentInteractionVertexOrderOfVertexOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (i : Fin (d.interactionComponentSize B)) :
    d.componentInteractionGlobalSlot order B
        (d.componentInteractionVertexOrderOfVertexOrder order B i) =
      ((d.componentInteractionGlobalSlots order B).orderIsoOfFin
        (d.card_componentInteractionGlobalSlots order B) i : Fin S.card) := by
  simp [TwoPointDiagram.componentInteractionVertexOrderOfVertexOrder]

/-- Family of component-local interaction orders induced by a global order. -/
def TwoPointDiagram.componentInteractionVertexOrdersOfVertexOrder {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) : d.ComponentInteractionVertexOrders :=
  fun B => d.componentInteractionVertexOrderOfVertexOrder order B

/-- Canonical induced local order is strictly increasing in global slot number. -/
theorem TwoPointDiagram.componentInteractionVertexOrderOfVertexOrder_strictMono
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    StrictMono (fun i => d.componentInteractionGlobalSlot order B
      (d.componentInteractionVertexOrderOfVertexOrder order B i)) := by
  intro i j hij
  rw [d.componentInteractionGlobalSlot_componentInteractionVertexOrderOfVertexOrder,
    d.componentInteractionGlobalSlot_componentInteractionVertexOrderOfVertexOrder]
  exact ((d.componentInteractionGlobalSlots order B).orderIsoOfFin
    (d.card_componentInteractionGlobalSlots order B)).strictMono hij

/-- Induced component-local orders are compatible with the ambient order. -/
theorem TwoPointDiagram.componentInteractionOrdersCompatible_ofVertexOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    d.ComponentInteractionOrdersCompatible order
      (d.componentInteractionVertexOrdersOfVertexOrder order) := by
  intro B
  simpa [TwoPointDiagram.ComponentInteractionOrdersCompatible,
    TwoPointDiagram.componentInteractionVertexEquiv,
    TwoPointDiagram.componentInteractionVertexOrdersOfVertexOrder,
    TwoPointDiagram.componentInteractionGlobalSlot] using
    d.componentInteractionVertexOrderOfVertexOrder_strictMono order B

/-- A compatible local interaction order is uniquely the increasing occupied-slot order. -/
theorem TwoPointDiagram.componentInteractionVertexOrder_eq_of_strictMono
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (localOrder : QuarticVertexOrder
      (TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))))
    (hlocal : StrictMono (fun i =>
      d.componentInteractionGlobalSlot order B (localOrder i))) :
    localOrder = d.componentInteractionVertexOrderOfVertexOrder order B := by
  apply Equiv.ext
  intro i
  apply d.componentInteractionGlobalSlot_injective order B
  have h := Finset.orderEmbOfFin_unique
    (s := d.componentInteractionGlobalSlots order B)
    (h := d.card_componentInteractionGlobalSlots order B)
    (f := fun i => d.componentInteractionGlobalSlot order B (localOrder i))
    (fun i => d.componentInteractionGlobalSlot_mem order B (localOrder i)) hlocal
  have hi := congrFun h i
  rw [d.componentInteractionGlobalSlot_componentInteractionVertexOrderOfVertexOrder]
  simpa only [Finset.coe_orderIsoOfFin_apply] using hi

/-- Compatible component-local interaction orders are uniquely determined by the global order. -/
theorem TwoPointDiagram.componentInteractionVertexOrders_eq_of_compatible
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (orders : d.ComponentInteractionVertexOrders)
    (h : d.ComponentInteractionOrdersCompatible order orders) :
    orders = d.componentInteractionVertexOrdersOfVertexOrder order := by
  funext B
  apply d.componentInteractionVertexOrder_eq_of_strictMono order B
  simpa [TwoPointDiagram.ComponentInteractionOrdersCompatible,
    TwoPointDiagram.componentInteractionVertexEquiv,
    TwoPointDiagram.componentInteractionGlobalSlot] using h B

/-- A global interaction order is equivalent to component-local interaction orders and one shuffle. -/
def TwoPointDiagram.componentInteractionOrderDecompositionEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    QuarticVertexOrder S ≃ d.ComponentInteractionVertexOrders × d.ComponentInteractionShuffle where
  toFun order :=
    let orders := d.componentInteractionVertexOrdersOfVertexOrder order
    ⟨orders, d.interactionShuffleOfVertexOrder order orders
      (d.componentInteractionOrdersCompatible_ofVertexOrder order)⟩
  invFun x := d.assembleInteractionVertexOrder x.1 x.2
  left_inv order := by
    dsimp
    exact d.assembleInteractionVertexOrder_interactionShuffleOfVertexOrder order
      (d.componentInteractionVertexOrdersOfVertexOrder order)
      (d.componentInteractionOrdersCompatible_ofVertexOrder order)
  right_inv x := by
    obtain ⟨orders, shuffle⟩ := x
    dsimp
    have horders :
        d.componentInteractionVertexOrdersOfVertexOrder
            (d.assembleInteractionVertexOrder orders shuffle) = orders :=
      (d.componentInteractionVertexOrders_eq_of_compatible
        (d.assembleInteractionVertexOrder orders shuffle) orders
        (d.componentInteractionOrdersCompatible_assemble orders shuffle)).symm
    refine Prod.ext horders ?_
    apply Combinatorics.FamilySlotShuffleTo.ext
    change (d.componentInteractionVertexEquiv
      (d.componentInteractionVertexOrdersOfVertexOrder
        (d.assembleInteractionVertexOrder orders shuffle))).trans
      (d.assembleInteractionVertexOrder orders shuffle).symm = shuffle.slotEquiv
    have hvertex := congrArg
      (fun componentOrders => d.componentInteractionVertexEquiv componentOrders) horders
    rw [hvertex]
    ext slot
    simp [TwoPointDiagram.assembleInteractionVertexOrder]

/-- Reindex a finite sum over global interaction orders by local component orders and shuffles. -/
theorem TwoPointDiagram.sum_interactionVertexOrder_eq_sum_componentOrders_shuffle
    [AddCommMonoid M] {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.ComponentInteractionVertexOrders × d.ComponentInteractionShuffle → M) :
    ∑ order : QuarticVertexOrder S, F (d.componentInteractionOrderDecompositionEquiv order) =
      ∑ x : d.ComponentInteractionVertexOrders × d.ComponentInteractionShuffle, F x :=
  Equiv.sum_comp d.componentInteractionOrderDecompositionEquiv F

end

end Common
end SecondQuantization
