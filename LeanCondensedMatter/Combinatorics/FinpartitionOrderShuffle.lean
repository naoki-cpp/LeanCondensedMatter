import LeanCondensedMatter.Combinatorics.FamilyOrderShuffle
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
  Combinatorics.FamilyOrdersOf
    (fun B : π.parts => ↥(B : Finset α))
    (fun B : π.parts => (B : Finset α).card)

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
  Combinatorics.assembleFamilyOrderOfSize
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    π.equivSigmaParts orders shuffle

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
  have hslot (i : Fin (B : Finset α).card) :
      (π.assembleOrder orders shuffle).symm (π.partEquiv orders ⟨B, i⟩) =
        shuffle.slotEquiv ⟨B, i⟩ := by
    simpa [Finpartition.assembleOrder, Finpartition.partEquiv] using
      (Combinatorics.assembleFamilyOrderOfSize_symm_apply
        (F := fun B : π.parts => ↥(B : Finset α))
        (size := fun B : π.parts => (B : Finset α).card)
        π.equivSigmaParts orders shuffle B i)
  intro i j hij
  simpa only [hslot i, hslot j] using shuffle.strictMono B hij

/-- Reassembling a global order from compatible part-local orders and its extracted shuffle is the
original global order. -/
@[simp]
theorem assembleOrder_shuffleOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders) :
    π.assembleOrder orders (π.shuffleOfOrder order orders h) = order := by
  apply Combinatorics.assembleFamilyOrderOfSize_eq_order
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    π.equivSigmaParts orders (π.shuffleOfOrder order orders h) order
  intro B j
  rfl

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
    (Set.equivOfEq (by
      ext x
      simp [Finpartition.partGlobalSlots]))

@[simp]
theorem partGlobalSlot_partGlobalSlotEquiv_symm (π : Finpartition s)
    (order : Fin s.card ≃ ↥s) (B : π.parts)
    (slot : ↥(π.partGlobalSlots order B)) :
    π.partGlobalSlot order B ((π.partGlobalSlotEquiv order B).symm slot) = slot := by
  let hslots : Set.range (π.partGlobalSlot order B) =
      ↑(π.partGlobalSlots order B) := by
    ext x
    simp [Finpartition.partGlobalSlots]
  change
    π.partGlobalSlot order B
        ((Equiv.ofInjective (π.partGlobalSlot order B)
          (π.partGlobalSlot_injective order B)).symm
          ((Set.equivOfEq hslots).symm slot)) =
      (slot : Fin s.card)
  rw [Equiv.apply_ofInjective_symm]
  exact congrArg Subtype.val (Set.equivOfEq_symm_apply hslots slot)

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
    (Fin s.card ≃ ↥s) ≃ π.PartOrders × π.PartShuffle :=
  Combinatorics.familyOrderDecompositionEquivOfSize
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    (hcard := fun B => Fintype.card_coe (B : Finset α))
    π.equivSigmaParts

/-- Summing a weight over all global orders factors through component-local order sums whenever,
for each fixed family of local orders, the shuffle sum is a common scalar times the product of
the corresponding local weights. -/
theorem sum_order_eq_mul_prod_sum_partOrders
    {R : Type*} [CommSemiring R]
    (π : Finpartition s)
    (globalWeight : (Fin s.card ≃ ↥s) → R)
    (localWeight :
      ∀ B : π.parts, (Fin (B : Finset α).card ≃ ↥(B : Finset α)) → R)
    (c : R)
    (hshuffle : ∀ orders : π.PartOrders,
      (∑ shuffle : π.PartShuffle, globalWeight (π.assembleOrder orders shuffle)) =
        c * ∏ B : π.parts, localWeight B (orders B)) :
    (∑ order : Fin s.card ≃ ↥s, globalWeight order) =
      c * ∏ B : π.parts,
        ∑ order : Fin (B : Finset α).card ≃ ↥(B : Finset α),
          localWeight B order := by
  classical
  calc
    (∑ order : Fin s.card ≃ ↥s, globalWeight order) =
        ∑ x : π.PartOrders × π.PartShuffle,
          globalWeight (π.assembleOrder x.1 x.2) := by
      rw [← Equiv.sum_comp (π.orderDecompositionEquiv).symm]
      rfl
    _ = ∑ orders : π.PartOrders,
          ∑ shuffle : π.PartShuffle,
            globalWeight (π.assembleOrder orders shuffle) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ orders : π.PartOrders,
          c * ∏ B : π.parts, localWeight B (orders B) := by
      apply Fintype.sum_congr
      intro orders
      exact hshuffle orders
    _ = c * ∑ orders : π.PartOrders,
          ∏ B : π.parts, localWeight B (orders B) := by
      rw [Finset.mul_sum]
    _ = c * ∏ B : π.parts,
          ∑ order : Fin (B : Finset α).card ≃ ↥(B : Finset α),
            localWeight B order := by
      congr 1
      simpa using
        (Finset.prod_univ_sum
          (fun B : π.parts =>
            (Finset.univ :
              Finset (Fin (B : Finset α).card ≃ ↥(B : Finset α))))
          localWeight).symm

end Finpartition
