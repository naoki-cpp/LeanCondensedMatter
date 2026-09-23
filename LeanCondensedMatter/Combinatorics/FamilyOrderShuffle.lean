import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Orders decomposed by finite families

A global order on a finite type that is presented as a disjoint union of finite fibers decomposes
canonically into one local order per fiber together with an order-preserving family shuffle.

Unlike a `Finpartition`, the family index is retained even when a fiber is empty. This is needed
for component decompositions in which some components contribute no slots of the selected sector.
-/

namespace Combinatorics

variable {ι α : Type*} [Fintype ι] [Fintype α]
variable (F : ι → Type*) [∀ i, Fintype (F i)]

/-- One order for every fiber of a finite family. -/
abbrev FamilyOrders :=
  ∀ i, Fin (Fintype.card (F i)) ≃ F i

/-- Identify local ordered slots with the disjoint union of the family fibers. -/
private noncomputable def familyOrderedEquiv (orders : FamilyOrders F) :
    (Σ i, Fin (Fintype.card (F i))) ≃ Σ i, F i :=
  Equiv.sigmaCongrRight orders

/-- Assemble a global order from local fiber orders and an order-preserving family shuffle. -/
noncomputable def assembleFamilyOrder {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (orders : FamilyOrders F)
    (shuffle : FamilySlotShuffleTo (fun i => Fintype.card (F i)) total) :
    Fin total ≃ α :=
  shuffle.slotEquiv.symm.trans ((familyOrderedEquiv F orders).trans ambientEquiv.symm)

/-- Ambient slots occupied by one family fiber under a global order. -/
private noncomputable def familyGlobalSlots {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) : Finset (Fin total) :=
  Finset.univ.image fun x : F i => order.symm (ambientEquiv.symm ⟨i, x⟩)

private theorem familyGlobalSlot_injective {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    Function.Injective (fun x : F i => order.symm (ambientEquiv.symm ⟨i, x⟩)) := by
  intro x y h
  have h₁ := order.symm.injective h
  have h₂ := ambientEquiv.symm.injective h₁
  exact eq_of_heq (Sigma.mk.inj_iff.mp h₂).2

private theorem card_familyGlobalSlots {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    (familyGlobalSlots F ambientEquiv order i).card = Fintype.card (F i) := by
  rw [familyGlobalSlots,
    Finset.card_image_of_injective _ (familyGlobalSlot_injective F ambientEquiv order i),
    Finset.card_univ]

private noncomputable def familyGlobalSlotEquiv {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    F i ≃ ↥(familyGlobalSlots F ambientEquiv order i) :=
  (Equiv.ofInjective
      (fun x : F i => order.symm (ambientEquiv.symm ⟨i, x⟩))
      (familyGlobalSlot_injective F ambientEquiv order i)).trans
    (Equiv.setCongr (by
      ext x
      simp [familyGlobalSlots]))

/-- Canonical increasing-slot order on one fiber induced by a global order. -/
private noncomputable def familyOrderOfOrder {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    Fin (Fintype.card (F i)) ≃ F i :=
  ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
      (card_familyGlobalSlots F ambientEquiv order i)).toEquiv.trans
    (familyGlobalSlotEquiv F ambientEquiv order i).symm

/-- Canonical family of local orders induced by a global order. -/
private noncomputable def familyOrdersOfOrder {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) : FamilyOrders F :=
  fun i => familyOrderOfOrder F ambientEquiv order i

private theorem familyOrderOfOrder_slot {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) (j : Fin (Fintype.card (F i))) :
    order.symm (ambientEquiv.symm ⟨i, familyOrderOfOrder F ambientEquiv order i j⟩) =
      ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
        (card_familyGlobalSlots F ambientEquiv order i) j : Fin total) := by
  change
    order.symm
        (ambientEquiv.symm
          ⟨i, (familyGlobalSlotEquiv F ambientEquiv order i).symm
            ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
              (card_familyGlobalSlots F ambientEquiv order i) j)⟩) = _
  have h := congrArg Subtype.val
    ((familyGlobalSlotEquiv F ambientEquiv order i).apply_symm_apply
      ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
        (card_familyGlobalSlots F ambientEquiv order i) j))
  exact h

/-- Extract the order-preserving family shuffle induced by a global order. -/
private noncomputable def familyShuffleOfOrder {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) :
    FamilySlotShuffleTo (fun i => Fintype.card (F i)) total where
  slotEquiv := (familyOrderedEquiv F (familyOrdersOfOrder F ambientEquiv order)).trans
    (ambientEquiv.symm.trans order.symm)
  strictMono := by
    intro i a b hab
    change
      order.symm
          (ambientEquiv.symm
            ⟨i, familyOrderOfOrder F ambientEquiv order i a⟩) <
        order.symm
          (ambientEquiv.symm
            ⟨i, familyOrderOfOrder F ambientEquiv order i b⟩)
    rw [familyOrderOfOrder_slot F ambientEquiv order i a,
      familyOrderOfOrder_slot F ambientEquiv order i b]
    exact ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
      (card_familyGlobalSlots F ambientEquiv order i)).strictMono hab

private theorem familyOrder_eq_of_strictMono {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι)
    (localOrder : Fin (Fintype.card (F i)) ≃ F i)
    (hlocal : StrictMono
      (fun j => order.symm (ambientEquiv.symm ⟨i, localOrder j⟩))) :
    localOrder = familyOrderOfOrder F ambientEquiv order i := by
  apply Equiv.ext
  intro j
  have hmem : ∀ k, order.symm (ambientEquiv.symm ⟨i, localOrder k⟩) ∈
      familyGlobalSlots F ambientEquiv order i := by
    intro k
    simp [familyGlobalSlots]
  have hunique := Finset.orderEmbOfFin_unique
    (s := familyGlobalSlots F ambientEquiv order i)
    (h := card_familyGlobalSlots F ambientEquiv order i)
    (f := fun k => order.symm (ambientEquiv.symm ⟨i, localOrder k⟩))
    hmem hlocal
  have hj := congrFun hunique j
  have hcanonical :
      order.symm
          (ambientEquiv.symm
            ⟨i, familyOrderOfOrder F ambientEquiv order i j⟩) =
        ((familyGlobalSlots F ambientEquiv order i).orderEmbOfFin
          (card_familyGlobalSlots F ambientEquiv order i)) j := by
    simpa only [Finset.coe_orderIsoOfFin_apply] using
      familyOrderOfOrder_slot F ambientEquiv order i j
  have hslot := hj.trans hcanonical.symm
  have h₁ := order.symm.injective hslot
  have h₂ := ambientEquiv.symm.injective h₁
  exact eq_of_heq (Sigma.mk.inj_iff.mp h₂).2

/-- Reassembling the extracted local orders and shuffle recovers the global order. -/
private theorem assembleFamilyOrder_ordersOfOrder_shuffleOfOrder {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) :
    assembleFamilyOrder F ambientEquiv
        (familyOrdersOfOrder F ambientEquiv order)
        (familyShuffleOfOrder F ambientEquiv order) = order := by
  ext j
  simp [assembleFamilyOrder, familyShuffleOfOrder, familyOrderedEquiv]

/-- A global order on a finite family is equivalent to local fiber orders together with an
order-preserving family shuffle. Empty fibers are retained as zero-size shuffle blocks. -/
noncomputable def familyOrderDecompositionEquiv {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i) :
    (Fin total ≃ α) ≃
      FamilyOrders F × FamilySlotShuffleTo (fun i => Fintype.card (F i)) total where
  toFun order :=
    (familyOrdersOfOrder F ambientEquiv order,
      familyShuffleOfOrder F ambientEquiv order)
  invFun x := assembleFamilyOrder F ambientEquiv x.1 x.2
  left_inv order :=
    assembleFamilyOrder_ordersOfOrder_shuffleOfOrder F ambientEquiv order
  right_inv x := by
    obtain ⟨orders, shuffle⟩ := x
    let order := assembleFamilyOrder F ambientEquiv orders shuffle
    have horders :
        familyOrdersOfOrder F ambientEquiv order = orders := by
      funext i
      symm
      apply familyOrder_eq_of_strictMono F ambientEquiv order i (orders i)
      intro a b hab
      have hslot (j : Fin (Fintype.card (F i))) :
          order.symm (ambientEquiv.symm ⟨i, orders i j⟩) =
            shuffle.slotEquiv ⟨i, j⟩ := by
        simp [order, assembleFamilyOrder, familyOrderedEquiv]
      rw [hslot a, hslot b]
      exact shuffle.strictMono i hab
    apply Prod.ext horders
    apply FamilySlotShuffleTo.ext
    change
      (familyOrderedEquiv F (familyOrdersOfOrder F ambientEquiv order)).trans
          (ambientEquiv.symm.trans order.symm) = shuffle.slotEquiv
    rw [horders]
    ext z
    simp [order, assembleFamilyOrder]

end Combinatorics
