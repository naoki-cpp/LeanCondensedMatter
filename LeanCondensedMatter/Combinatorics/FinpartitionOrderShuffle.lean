import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false

/-!
# Orders and shuffles over finite partitions

A global ordering of a finite set canonically decomposes into an ordering on every part of a finite
partition together with an order-preserving shuffle of the part-local slots.  This module contains
only the finite combinatorics of that decomposition; no diagram, graph, or particle-statistics
structure is involved.
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- An ordering of the elements in every part of a finite partition. -/
abbrev PartOrders (π : Finpartition s) :=
  ∀ B : π.parts, Fin (B : Finset α).card ≃ ↥(B : Finset α)

/-- An order-preserving interleaving of all part-local slots into the ambient slots. -/
abbrev PartShuffle (π : Finpartition s) :=
  Combinatorics.FamilySlotShuffleTo
    (fun B : π.parts => (B : Finset α).card) s.card

/-- The disjoint union of part-local slots, identified with the ambient finite set using the chosen
local order on every part. -/
noncomputable def partEquiv (π : Finpartition s) (orders : π.PartOrders) :
    (Σ B : π.parts, Fin (B : Finset α).card) ≃ ↥s :=
  (Equiv.sigmaCongrRight fun B => orders B).trans π.equivSigmaParts.symm

/-- Assemble a global order from part-local orders and an order-preserving shuffle. -/
noncomputable def assembleOrder (π : Finpartition s) (orders : π.PartOrders)
    (shuffle : π.PartShuffle) : Fin s.card ≃ ↥s :=
  shuffle.slotEquiv.symm.trans (π.partEquiv orders)

/-- A family of part-local orders is compatible with a global order when every part appears in the
ambient slots in precisely that local order. -/
noncomputable def PartOrdersCompatible (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) : Prop :=
  ∀ B, StrictMono (fun i => order.symm (π.partEquiv orders ⟨B, i⟩))

/-- Read off the unique part shuffle from a global order and compatible part-local orders. -/
noncomputable def shuffleOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders) : π.PartShuffle where
  slotEquiv := (π.partEquiv orders).trans order.symm
  strictMono := h

/-- The local orders used to assemble a global order are compatible with that assembled order. -/
theorem partOrdersCompatible_assembleOrder (π : Finpartition s) (orders : π.PartOrders)
    (shuffle : π.PartShuffle) :
    π.PartOrdersCompatible (π.assembleOrder orders shuffle) orders := by
  intro B
  simpa [Finpartition.PartOrdersCompatible,
    Finpartition.assembleOrder] using shuffle.strictMono B

/-- Reassembling a global order from compatible part-local orders and its extracted shuffle is the
original global order. -/
@[simp]
theorem assembleOrder_shuffleOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders) :
    π.assembleOrder orders (π.shuffleOfOrder order orders h) = order := by
  ext i
  simp [Finpartition.assembleOrder, Finpartition.shuffleOfOrder]

/-- The ambient slot occupied by an element of part `B`. -/
noncomputable def partGlobalSlot (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) (v : ↥(B : Finset α)) : Fin s.card :=
  order.symm (π.equivSigmaParts.symm ⟨B, v⟩)

/-- Distinct elements of one part occupy distinct ambient slots. -/
theorem partGlobalSlot_injective (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) : Function.Injective (π.partGlobalSlot order B) := by
  intro v w h
  have h₁ := order.symm.injective h
  have h₂ := π.equivSigmaParts.symm.injective h₁
  cases h₂
  rfl

/-- The finite set of ambient slots occupied by one partition part. -/
noncomputable def partGlobalSlots (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) : Finset (Fin s.card) :=
  Finset.univ.image (π.partGlobalSlot order B)

@[simp]
theorem partGlobalSlot_mem_partGlobalSlots (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) (v : ↥(B : Finset α)) :
    π.partGlobalSlot order B v ∈ π.partGlobalSlots order B :=
  Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩

/-- A part occupies exactly as many ambient slots as it has elements. -/
theorem card_partGlobalSlots (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) :
    (π.partGlobalSlots order B).card = (B : Finset α).card := by
  rw [Finpartition.partGlobalSlots,
    Finset.card_image_of_injective _ (π.partGlobalSlot_injective order B)]
  simp

/-- Elements of a partition part are equivalent to the ambient slots occupied by that part. -/
noncomputable def partGlobalSlotEquiv (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) : ↥(B : Finset α) ≃ ↥(π.partGlobalSlots order B) :=
  (Equiv.ofInjective (π.partGlobalSlot order B)
      (π.partGlobalSlot_injective order B)).trans
    (Equiv.setCongr (by
      ext x
      simp [Finpartition.partGlobalSlots]))

@[simp]
theorem partGlobalSlot_partGlobalSlotEquiv_symm (π : Finpartition s)
    (order : Fin s.card ≃ ↥s) (B : π.parts)
    (slot : ↥(π.partGlobalSlots order B)) :
    π.partGlobalSlot order B ((π.partGlobalSlotEquiv order B).symm slot) = slot := by
  have h := congrArg Subtype.val ((π.partGlobalSlotEquiv order B).apply_symm_apply slot)
  exact h

/-- The canonical order on one part induced by its increasing ambient slots. -/
noncomputable def partOrderOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) : Fin (B : Finset α).card ≃ ↥(B : Finset α) :=
  (π.partGlobalSlots order B).orderIsoOfFin
      (π.card_partGlobalSlots order B) |>.toEquiv.trans
    (π.partGlobalSlotEquiv order B).symm

@[simp]
theorem partGlobalSlot_partOrderOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) (i : Fin (B : Finset α).card) :
    π.partGlobalSlot order B (π.partOrderOfOrder order B i) =
      ((π.partGlobalSlots order B).orderIsoOfFin
        (π.card_partGlobalSlots order B) i : Fin s.card) := by
  simp [Finpartition.partOrderOfOrder]

/-- The canonical family of part-local orders induced by an ambient order. -/
noncomputable def partOrdersOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s) :
    π.PartOrders :=
  fun B => π.partOrderOfOrder order B

/-- The canonical local order on each part is strictly increasing in ambient slot number. -/
theorem partOrderOfOrder_strictMono (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) :
    StrictMono (fun i => π.partGlobalSlot order B (π.partOrderOfOrder order B i)) := by
  intro i j hij
  change π.partGlobalSlot order B (π.partOrderOfOrder order B i) <
    π.partGlobalSlot order B (π.partOrderOfOrder order B j)
  rw [π.partGlobalSlot_partOrderOfOrder, π.partGlobalSlot_partOrderOfOrder]
  exact ((π.partGlobalSlots order B).orderIsoOfFin
    (π.card_partGlobalSlots order B)).strictMono hij

/-- The canonical part-local orders are compatible with the ambient order. -/
theorem partOrdersCompatible_partOrdersOfOrder (π : Finpartition s)
    (order : Fin s.card ≃ ↥s) :
    π.PartOrdersCompatible order (π.partOrdersOfOrder order) := by
  intro B
  simpa [Finpartition.PartOrdersCompatible, Finpartition.partEquiv,
    Finpartition.partOrdersOfOrder, Finpartition.partGlobalSlot] using
    π.partOrderOfOrder_strictMono order B

/-- A compatible order on one part must be its canonical increasing-slot order. -/
theorem partOrder_eq_of_strictMono (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (B : π.parts) (localOrder : Fin (B : Finset α).card ≃ ↥(B : Finset α))
    (hlocal : StrictMono (fun i => π.partGlobalSlot order B (localOrder i))) :
    localOrder = π.partOrderOfOrder order B := by
  apply Equiv.ext
  intro i
  apply π.partGlobalSlot_injective order B
  have h := Finset.orderEmbOfFin_unique
    (s := π.partGlobalSlots order B)
    (h := π.card_partGlobalSlots order B)
    (f := fun i => π.partGlobalSlot order B (localOrder i))
    (fun i => π.partGlobalSlot_mem_partGlobalSlots order B (localOrder i)) hlocal
  have hi := congrFun h i
  rw [π.partGlobalSlot_partOrderOfOrder]
  simpa only [Finset.coe_orderIsoOfFin_apply] using hi

/-- A compatible family of part-local orders is uniquely determined by the ambient order. -/
theorem partOrders_eq_of_compatible (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders) :
    orders = π.partOrdersOfOrder order := by
  funext B
  apply π.partOrder_eq_of_strictMono order B
  simpa [Finpartition.PartOrdersCompatible, Finpartition.partEquiv,
    Finpartition.partGlobalSlot] using h B

/-- A global finite-set order is equivalent to part-local orders together with an order-preserving
shuffle of their slots. -/
noncomputable def orderDecompositionEquiv (π : Finpartition s) :
    (Fin s.card ≃ ↥s) ≃ π.PartOrders × π.PartShuffle where
  toFun order :=
    let orders := π.partOrdersOfOrder order
    ⟨orders, π.shuffleOfOrder order orders (π.partOrdersCompatible_partOrdersOfOrder order)⟩
  invFun x := π.assembleOrder x.1 x.2
  left_inv order := by
    dsimp
    exact π.assembleOrder_shuffleOfOrder order
      (π.partOrdersOfOrder order) (π.partOrdersCompatible_partOrdersOfOrder order)
  right_inv x := by
    obtain ⟨orders, shuffle⟩ := x
    dsimp
    have horders : π.partOrdersOfOrder (π.assembleOrder orders shuffle) = orders :=
      (π.partOrders_eq_of_compatible
        (π.assembleOrder orders shuffle) orders
        (π.partOrdersCompatible_assembleOrder orders shuffle)).symm
    refine Prod.ext horders ?_
    apply Combinatorics.FamilySlotShuffleTo.ext
    change (π.partEquiv
      (π.partOrdersOfOrder (π.assembleOrder orders shuffle))).trans
        (π.assembleOrder orders shuffle).symm = shuffle.slotEquiv
    have hpart := congrArg (fun partOrders => π.partEquiv partOrders) horders
    rw [hpart]
    ext slot
    simp [Finpartition.assembleOrder]

end Finpartition
