import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentRestriction

set_option linter.style.header false

/-!
# Component-local vertex orders and global shuffles

A global vertex order can be assembled from an order on every connected-component block together with
an interleaving of the component-local slots.  The interleaving is represented by an equivalence from
the sigma type of local slots to the global slots, with strict monotonicity on every component fiber.
This is the order-preserving shuffle structure needed by the later ordered-simplex factorization.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- A vertex order on every connected-component block of `d`. -/
abbrev QuarticDiagram.ComponentVertexOrders {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :=
  ∀ B : d.componentPartition.parts, QuarticVertexOrder (B : Finset (Fin N))

/-- An order-preserving interleaving of all component-local slots into the ambient global slots. -/
structure QuarticDiagram.ComponentShuffle {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) where
  /-- Equivalence between component-local slots and global vertex slots. -/
  slotEquiv :
    (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) ≃ Fin S.card
  strictMono : ∀ B, StrictMono (fun i => slotEquiv ⟨B, i⟩)

@[ext]
theorem QuarticDiagram.ComponentShuffle.ext {S : Finset (Fin N)}
    {d : QuarticDiagram Label N S} {σ τ : d.ComponentShuffle}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- The disjoint union of component-local slots, identified with the ambient vertex set using the
chosen local order on every component. -/
noncomputable def QuarticDiagram.componentVertexEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders) :
    (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) ≃ ↥S :=
  (Equiv.sigmaCongrRight fun B => orders B).trans d.componentPartition.equivSigmaParts.symm

/-- Assemble a global vertex order from component-local orders and an order-preserving shuffle. -/
noncomputable def QuarticDiagram.assembleVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) : QuarticVertexOrder S :=
  shuffle.slotEquiv.symm.trans (d.componentVertexEquiv orders)

@[simp]
theorem QuarticDiagram.assembleVertexOrder_apply {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (i : Fin S.card) :
    d.assembleVertexOrder orders shuffle i =
      d.componentVertexEquiv orders (shuffle.slotEquiv.symm i) :=
  rfl

@[simp]
theorem QuarticDiagram.assembleVertexOrder_symm_componentVertexEquiv
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (x : Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) :
    (d.assembleVertexOrder orders shuffle).symm (d.componentVertexEquiv orders x) =
      shuffle.slotEquiv x := by
  simp [QuarticDiagram.assembleVertexOrder]

/-- A family of component-local orders is compatible with a global order when each component appears
in the global slots in precisely that local order. -/
noncomputable def QuarticDiagram.ComponentOrdersCompatible {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) : Prop :=
  ∀ B, StrictMono (fun i => order.symm (d.componentVertexEquiv orders ⟨B, i⟩))

/-- Read off the unique component shuffle from a global order and compatible component-local orders. -/
noncomputable def QuarticDiagram.shuffleOfVertexOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.ComponentShuffle where
  slotEquiv := (d.componentVertexEquiv orders).trans order.symm
  strictMono := h

/-- The local orders used to assemble a global order are compatible with that assembled order. -/
theorem QuarticDiagram.componentOrdersCompatible_assembleVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    d.ComponentOrdersCompatible (d.assembleVertexOrder orders shuffle) orders := by
  intro B
  simpa [QuarticDiagram.ComponentOrdersCompatible,
    QuarticDiagram.assembleVertexOrder] using shuffle.strictMono B

/-- Recovering the shuffle from an assembled global order returns the original shuffle. -/
@[simp]
theorem QuarticDiagram.shuffleOfVertexOrder_assembleVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    d.shuffleOfVertexOrder (d.assembleVertexOrder orders shuffle) orders
      (d.componentOrdersCompatible_assembleVertexOrder orders shuffle) = shuffle := by
  apply QuarticDiagram.ComponentShuffle.ext
  ext x
  simp [QuarticDiagram.shuffleOfVertexOrder, QuarticDiagram.assembleVertexOrder]

/-- Reassembling a global order from its compatible component-local orders and extracted shuffle is
identity. -/
@[simp]
theorem QuarticDiagram.assembleVertexOrder_shuffleOfVertexOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S)
    (orders : d.ComponentVertexOrders) (h : d.ComponentOrdersCompatible order orders) :
    d.assembleVertexOrder orders (d.shuffleOfVertexOrder order orders h) = order := by
  ext i
  simp [QuarticDiagram.assembleVertexOrder, QuarticDiagram.shuffleOfVertexOrder]

end Common
end SecondQuantization
