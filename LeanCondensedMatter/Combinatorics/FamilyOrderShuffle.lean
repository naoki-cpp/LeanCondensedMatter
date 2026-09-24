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

/-- One order for every fiber when the block size is supplied explicitly. -/
abbrev FamilyOrdersOf (F : ι → Type*) (size : ι → ℕ) :=
  ∀ i, Fin (size i) ≃ F i

/-- One order for every fiber, using the canonical finite cardinality as its block size. -/
abbrev FamilyOrders := FamilyOrdersOf F (fun i => Fintype.card (F i))

/-- Identify local ordered slots with the disjoint union of the family fibers. -/
private noncomputable def familyOrderedEquiv (size : ι → ℕ) (orders : FamilyOrdersOf F size) :
    (Σ i, Fin (size i)) ≃ Σ i, F i :=
  Equiv.sigmaCongrRight orders

/-- Assemble a global order with an explicitly indexed family of block sizes. -/
noncomputable def assembleFamilyOrderOfSize {total : ℕ} (size : ι → ℕ)
    (ambientEquiv : α ≃ Σ i, F i)
    (orders : FamilyOrdersOf F size)
    (shuffle : FamilySlotShuffleTo size total) :
    Fin total ≃ α :=
  shuffle.slotEquiv.symm.trans ((familyOrderedEquiv F size orders).trans ambientEquiv.symm)

omit [Fintype ι] [Fintype α] [∀ i, Fintype (F i)] in
@[simp]
theorem assembleFamilyOrderOfSize_symm_apply {total : ℕ} (size : ι → ℕ)
    (ambientEquiv : α ≃ Σ i, F i)
    (orders : FamilyOrdersOf F size)
    (shuffle : FamilySlotShuffleTo size total)
    (i : ι) (j : Fin (size i)) :
    (assembleFamilyOrderOfSize F size ambientEquiv orders shuffle).symm
        (ambientEquiv.symm ⟨i, orders i j⟩) = shuffle.slotEquiv ⟨i, j⟩ := by
  have hsigma :
      (Equiv.sigmaCongrRight orders).symm ⟨i, orders i j⟩ = ⟨i, j⟩ := by
    rw [show (⟨i, orders i j⟩ : Σ i, F i) =
      (Equiv.sigmaCongrRight orders) ⟨i, j⟩ by rfl]
    exact (Equiv.sigmaCongrRight orders).symm_apply_apply ⟨i, j⟩
  simp [assembleFamilyOrderOfSize, familyOrderedEquiv, hsigma]

omit [Fintype ι] [Fintype α] [∀ i, Fintype (F i)] in
theorem assembleFamilyOrderOfSize_eq_order {total : ℕ} (size : ι → ℕ)
    (ambientEquiv : α ≃ Σ i, F i)
    (orders : FamilyOrdersOf F size)
    (shuffle : FamilySlotShuffleTo size total)
    (order : Fin total ≃ α)
    (hslot : ∀ i j,
      order.symm (ambientEquiv.symm ⟨i, orders i j⟩) = shuffle.slotEquiv ⟨i, j⟩) :
    assembleFamilyOrderOfSize F size ambientEquiv orders shuffle = order := by
  have hshuffle :
      (familyOrderedEquiv F size orders).trans (ambientEquiv.symm.trans order.symm) =
        shuffle.slotEquiv := by
    ext z
    obtain ⟨i, j⟩ := z
    simpa [familyOrderedEquiv, Equiv.trans_apply] using
      congrArg (fun x => x.val) (hslot i j)
  ext i
  change (familyOrderedEquiv F size orders).trans ambientEquiv.symm
      (shuffle.slotEquiv.symm i) = order i
  rw [← hshuffle]
  simp [Equiv.trans_assoc]

/-- Assemble a global order from local fiber orders and an order-preserving family shuffle. -/
noncomputable def assembleFamilyOrder {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (orders : FamilyOrders F)
    (shuffle : FamilySlotShuffleTo (fun i => Fintype.card (F i)) total) :
    Fin total ≃ α :=
  assembleFamilyOrderOfSize F (fun i => Fintype.card (F i)) ambientEquiv orders shuffle

/-- Ambient slots occupied by one family fiber under a global order. -/
private noncomputable def familyGlobalSlots {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) : Finset (Fin total) :=
  Finset.univ.image fun x : F i => order.symm (ambientEquiv.symm ⟨i, x⟩)

omit [Fintype ι] [Fintype α] [∀ i, Fintype (F i)] in
private theorem familyGlobalSlot_injective {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    Function.Injective (fun x : F i => order.symm (ambientEquiv.symm ⟨i, x⟩)) := by
  intro x y h
  have h₁ := order.symm.injective h
  have h₂ := ambientEquiv.symm.injective h₁
  exact eq_of_heq (Sigma.mk.inj_iff.mp h₂).2

omit [Fintype ι] [Fintype α] in
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
private noncomputable def familyOrderOfOrder {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    Fin (size i) ≃ F i :=
  ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
      ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i))).toEquiv.trans
    (familyGlobalSlotEquiv F ambientEquiv order i).symm

/-- Canonical family of local orders induced by a global order. -/
private noncomputable def familyOrdersOfOrder {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) : FamilyOrdersOf F size :=
  fun i => familyOrderOfOrder F size hcard ambientEquiv order i

omit [Fintype ι] [Fintype α] in
private theorem familyOrderOfOrder_slot {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) (j : Fin (size i)) :
    order.symm (ambientEquiv.symm ⟨i, familyOrderOfOrder F size hcard ambientEquiv order i j⟩) =
      ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
        ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i)) j : Fin total) := by
  change
    order.symm
        (ambientEquiv.symm
          ⟨i, (familyGlobalSlotEquiv F ambientEquiv order i).symm
            ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
              ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i)) j)⟩) = _
  have h := congrArg Subtype.val
      ((familyGlobalSlotEquiv F ambientEquiv order i).apply_symm_apply
      ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
        ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i)) j))
  exact h

/-- Extract the order-preserving family shuffle induced by a global order. -/
private noncomputable def familyShuffleOfOrder {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) :
    FamilySlotShuffleTo size total where
  slotEquiv :=
    (familyOrderedEquiv F size (familyOrdersOfOrder F size hcard ambientEquiv order)).trans
    (ambientEquiv.symm.trans order.symm)
  strictMono := by
    intro i a b hab
    change
      order.symm
          (ambientEquiv.symm
            ⟨i, familyOrderOfOrder F size hcard ambientEquiv order i a⟩) <
        order.symm
          (ambientEquiv.symm
            ⟨i, familyOrderOfOrder F size hcard ambientEquiv order i b⟩)
    rw [familyOrderOfOrder_slot F size hcard ambientEquiv order i a,
      familyOrderOfOrder_slot F size hcard ambientEquiv order i b]
    exact ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
      ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i))).strictMono hab

omit [Fintype ι] [Fintype α] in
private theorem familyOrder_eq_of_strictMono {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι)
    (localOrder : Fin (size i) ≃ F i)
    (hlocal : StrictMono
      (fun j => order.symm (ambientEquiv.symm ⟨i, localOrder j⟩))) :
    localOrder = familyOrderOfOrder F size hcard ambientEquiv order i := by
  apply Equiv.ext
  intro j
  have hmem : ∀ k, order.symm (ambientEquiv.symm ⟨i, localOrder k⟩) ∈
      familyGlobalSlots F ambientEquiv order i := by
    intro k
    simp [familyGlobalSlots]
  have hunique := Finset.orderEmbOfFin_unique
    (s := familyGlobalSlots F ambientEquiv order i)
    (h := (card_familyGlobalSlots F ambientEquiv order i).trans (hcard i))
    (f := fun k => order.symm (ambientEquiv.symm ⟨i, localOrder k⟩))
    hmem hlocal
  have hj := congrFun hunique j
  have hcanonical :
      order.symm
          (ambientEquiv.symm
            ⟨i, familyOrderOfOrder F size hcard ambientEquiv order i j⟩) =
        ((familyGlobalSlots F ambientEquiv order i).orderEmbOfFin
          ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i))) j := by
    simpa only [Finset.coe_orderIsoOfFin_apply] using
      familyOrderOfOrder_slot F size hcard ambientEquiv order i j
  have hslot := hj.trans hcanonical.symm
  have h₁ := order.symm.injective hslot
  have h₂ := ambientEquiv.symm.injective h₁
  exact eq_of_heq (Sigma.mk.inj_iff.mp h₂).2

omit [Fintype ι] [Fintype α] in
/-- Reassembling the extracted local orders and shuffle recovers the global order. -/
private theorem assembleFamilyOrder_ordersOfOrder_shuffleOfOrder {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) :
    assembleFamilyOrderOfSize F size ambientEquiv
        (familyOrdersOfOrder F size hcard ambientEquiv order)
        (familyShuffleOfOrder F size hcard ambientEquiv order) = order := by
  ext j
  simp [assembleFamilyOrderOfSize, familyShuffleOfOrder, familyOrderedEquiv]

/-- A global order on a finite family is equivalent to local fiber orders together with an
order-preserving family shuffle. Empty fibers are retained as zero-size shuffle blocks. -/
noncomputable def familyOrderDecompositionEquivOfSize {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i) :
    (Fin total ≃ α) ≃
      FamilyOrdersOf F size × FamilySlotShuffleTo size total where
  toFun order :=
    (familyOrdersOfOrder F size hcard ambientEquiv order,
      familyShuffleOfOrder F size hcard ambientEquiv order)
  invFun x := assembleFamilyOrderOfSize F size ambientEquiv x.1 x.2
  left_inv order :=
    assembleFamilyOrder_ordersOfOrder_shuffleOfOrder F size hcard ambientEquiv order
  right_inv x := by
    obtain ⟨orders, shuffle⟩ := x
    let order := assembleFamilyOrderOfSize F size ambientEquiv orders shuffle
    have horders :
        familyOrdersOfOrder F size hcard ambientEquiv order = orders := by
      funext i
      symm
      apply familyOrder_eq_of_strictMono F size hcard ambientEquiv order i (orders i)
      intro a b hab
      have hslot (j : Fin (size i)) :
          order.symm (ambientEquiv.symm ⟨i, orders i j⟩) =
            shuffle.slotEquiv ⟨i, j⟩ := by
        have hsigma :
            (Equiv.sigmaCongrRight orders).symm ⟨i, orders i j⟩ = ⟨i, j⟩ := by
          rw [show (⟨i, orders i j⟩ : Σ i, F i) =
            (Equiv.sigmaCongrRight orders) ⟨i, j⟩ by rfl]
          exact (Equiv.sigmaCongrRight orders).symm_apply_apply ⟨i, j⟩
        simp [order, assembleFamilyOrderOfSize, familyOrderedEquiv, hsigma]
      change
        order.symm (ambientEquiv.symm ⟨i, orders i a⟩) <
          order.symm (ambientEquiv.symm ⟨i, orders i b⟩)
      rw [hslot a, hslot b]
      exact shuffle.strictMono i hab
    apply Prod.ext horders
    apply FamilySlotShuffleTo.ext
    change
      (familyOrderedEquiv F size (familyOrdersOfOrder F size hcard ambientEquiv order)).trans
          (ambientEquiv.symm.trans order.symm) = shuffle.slotEquiv
    rw [horders]
    ext z
    simp [order, assembleFamilyOrderOfSize]

/-- A global order on a finite family is equivalent to local fiber orders together with an
order-preserving family shuffle. -/
noncomputable def familyOrderDecompositionEquiv {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i) :
    (Fin total ≃ α) ≃
      FamilyOrders F × FamilySlotShuffleTo (fun i => Fintype.card (F i)) total :=
  familyOrderDecompositionEquivOfSize F (fun i => Fintype.card (F i)) (fun _ => rfl) ambientEquiv

end Combinatorics
