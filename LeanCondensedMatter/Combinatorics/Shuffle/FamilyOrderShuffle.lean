import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffle
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
    (Set.equivOfEq (by
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
noncomputable def familyOrdersOfOrder {total : ℕ} (size : ι → ℕ)
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
  let y :=
    (familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
      ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i)) j
  have h := congrArg Subtype.val
      ((familyGlobalSlotEquiv F ambientEquiv order i).apply_symm_apply y)
  have hval (x : F i) :
      ((familyGlobalSlotEquiv F ambientEquiv order i x :
        ↥(familyGlobalSlots F ambientEquiv order i)) : Fin total) =
        order.symm (ambientEquiv.symm ⟨i, x⟩) := by
    simp only [familyGlobalSlotEquiv, Equiv.trans_apply, Equiv.ofInjective_apply]
    rw [Set.equivOfEq_apply]
  rw [hval] at h
  exact h

omit [Fintype ι] [Fintype α] in
/-- The extracted local order of each fiber is strictly increasing in ambient slot number. -/
theorem familyOrdersOfOrder_strictMono {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) (i : ι) :
    StrictMono (fun j => order.symm
      (ambientEquiv.symm ⟨i, familyOrdersOfOrder F size hcard ambientEquiv order i j⟩)) := by
  intro a b hab
  change
    order.symm (ambientEquiv.symm ⟨i, familyOrderOfOrder F size hcard ambientEquiv order i a⟩) <
      order.symm (ambientEquiv.symm ⟨i, familyOrderOfOrder F size hcard ambientEquiv order i b⟩)
  rw [familyOrderOfOrder_slot F size hcard ambientEquiv order i a,
    familyOrderOfOrder_slot F size hcard ambientEquiv order i b]
  exact ((familyGlobalSlots F ambientEquiv order i).orderIsoOfFin
    ((card_familyGlobalSlots F ambientEquiv order i).trans (hcard i))).strictMono hab

/-- Extract the order-preserving family shuffle induced by a global order. -/
private noncomputable def familyShuffleOfOrder {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α) :
    FamilySlotShuffleTo size total where
  slotEquiv :=
    (familyOrderedEquiv F size (familyOrdersOfOrder F size hcard ambientEquiv order)).trans
    (ambientEquiv.symm.trans order.symm)
  strictMono := familyOrdersOfOrder_strictMono F size hcard ambientEquiv order

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

/-- Under the decomposition of a global order, the ambient vertex at
a shuffled slot is *exactly* the local vertex carried by that block.
This is stronger than a cardinality identity and retains empty fibers. -/
theorem familyOrderDecompositionEquivOfSize_shuffle_slot
    {total : ℕ} (size : ι → ℕ)
    (hcard : ∀ i, Fintype.card (F i) = size i)
    (ambientEquiv : α ≃ Σ i, F i)
    (order : Fin total ≃ α)
    (i : ι) (j : Fin (size i)) :
    order ((familyOrderDecompositionEquivOfSize F size hcard ambientEquiv
      order).2.slotEquiv ⟨i, j⟩) =
      ambientEquiv.symm
        ⟨i, (familyOrderDecompositionEquivOfSize F size hcard ambientEquiv
          order).1 i j⟩ := by
  let e := familyOrderDecompositionEquivOfSize F size hcard ambientEquiv
  let data := e order
  have hassemble :
      assembleFamilyOrderOfSize F size ambientEquiv data.1 data.2 = order :=
    e.symm_apply_apply order
  have hslot := assembleFamilyOrderOfSize_symm_apply
    F size ambientEquiv data.1 data.2 i j
  rw [hassemble] at hslot
  have h := congrArg order hslot
  simpa [data, e] using h.symm

/-- A global order on a finite family is equivalent to local fiber orders together with an
order-preserving family shuffle. -/
noncomputable def familyOrderDecompositionEquiv {total : ℕ}
    (ambientEquiv : α ≃ Σ i, F i) :
    (Fin total ≃ α) ≃
      FamilyOrders F × FamilySlotShuffleTo (fun i => Fintype.card (F i)) total :=
  familyOrderDecompositionEquivOfSize F (fun i => Fintype.card (F i)) (fun _ => rfl) ambientEquiv

open Classical in
/-- The canonically increasing shuffle determined by an assignment of
ambient slots to family blocks. This is the assignment-side counterpart of
`familyOrderDecompositionEquiv`, specialized to the identity ambient order.
A block with no assigned slots retains its zero-size local fiber. -/
@[nolint unusedArguments]
noncomputable def ownerCanonicalShuffle
    {ι : Type*} [Fintype ι] {total : ℕ} (owner : Fin total → ι) :
    FamilySlotShuffleTo
      (fun i => Fintype.card {v : Fin total // owner v = i}) total := by
  classical
  exact
    (familyOrderDecompositionEquiv
      (fun i : ι => {v : Fin total // owner v = i})
      (Equiv.sigmaFiberEquiv owner).symm
      (Equiv.refl (Fin total))).2

open Classical in
/-- Each slot in the shuffle of a particular owner fiber retains that
owner, even if the other fibers have zero cardinality. -/
theorem ownerCanonicalShuffle_apply_owner
    {ι : Type*} [Fintype ι] {total : ℕ} (owner : Fin total → ι)
    (i : ι) (j : Fin (Fintype.card {v : Fin total // owner v = i})) :
    owner ((ownerCanonicalShuffle owner).slotEquiv ⟨i, j⟩) = i := by
  classical
  let orders :=
    familyOrdersOfOrder
      (fun i : ι => {v : Fin total // owner v = i})
      (fun i => Fintype.card {v : Fin total // owner v = i})
      (fun _ => rfl)
      (Equiv.sigmaFiberEquiv owner).symm (Equiv.refl (Fin total))
  have h := (orders i j).property
  change owner ((orders i j).1) = i
  exact h

open Classical in
/-- Recover the exact assigned owner of every ambient interaction slot
by unshuffling the canonical owner shuffle. -/
theorem ownerCanonicalShuffle_symm_owner
    {ι : Type*} [Fintype ι] {total : ℕ} (owner : Fin total → ι)
    (v : Fin total) :
    ((ownerCanonicalShuffle owner).slotEquiv.symm v).1 = owner v := by
  classical
  let σ := ownerCanonicalShuffle owner
  rcases hslot : σ.slotEquiv.symm v with ⟨i, j⟩
  have hback : σ.slotEquiv ⟨i, j⟩ = v := by
    calc
      σ.slotEquiv ⟨i, j⟩ =
          σ.slotEquiv (σ.slotEquiv.symm v) :=
        congrArg σ.slotEquiv hslot.symm
      _ = v := σ.slotEquiv.apply_symm_apply v
  simpa [σ, hback] using
    (ownerCanonicalShuffle_apply_owner owner i j).symm

/-- An order-preserving family shuffle is uniquely determined by the
ambient owner of each slot. Indeed, each block is necessarily enumerated
in increasing ambient-slot order. Empty blocks cause no exception. -/
theorem FamilySlotShuffleTo.eq_of_same_owner
    {ι : Type*} {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total)
    (howner : ∀ v : Fin total,
      (σ.slotEquiv.symm v).1 = (τ.slotEquiv.symm v).1) :
    σ = τ := by
  classical
  apply FamilySlotShuffleTo.ext
  apply Equiv.ext
  rintro ⟨i, j⟩
  let s : Finset (Fin total) :=
    Finset.univ.image (fun k : Fin (size i) => σ.slotEquiv ⟨i, k⟩)
  have hsize : s.card = size i := by
    dsimp [s]
    rw [Finset.card_image_of_injective _
      (fun a b hab => (σ.strictMono i).injective hab)]
    simp
  have hσmem (k : Fin (size i)) : σ.slotEquiv ⟨i, k⟩ ∈ s :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hτmem (k : Fin (size i)) : τ.slotEquiv ⟨i, k⟩ ∈ s := by
    have hi : (σ.slotEquiv.symm (τ.slotEquiv ⟨i, k⟩)).1 = i := by
      simpa using howner (τ.slotEquiv ⟨i, k⟩)
    rcases heq : σ.slotEquiv.symm (τ.slotEquiv ⟨i, k⟩) with ⟨i', q⟩
    have hii : i' = i := by simpa [heq] using hi
    subst i'
    have hback : σ.slotEquiv ⟨i, q⟩ = τ.slotEquiv ⟨i, k⟩ := by
      calc
        σ.slotEquiv ⟨i, q⟩ =
            σ.slotEquiv (σ.slotEquiv.symm (τ.slotEquiv ⟨i, k⟩)) :=
          congrArg σ.slotEquiv heq.symm
        _ = _ := σ.slotEquiv.apply_symm_apply _
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hback⟩
  have hσ := Finset.orderEmbOfFin_unique
    (s := s) (h := hsize)
    (f := fun k : Fin (size i) => σ.slotEquiv ⟨i, k⟩)
    hσmem (σ.strictMono i)
  have hτ := Finset.orderEmbOfFin_unique
    (s := s) (h := hsize)
    (f := fun k : Fin (size i) => τ.slotEquiv ⟨i, k⟩)
    hτmem (τ.strictMono i)
  exact congrFun (hσ.trans hτ.symm) j

open Classical in
/-- Every shuffle has exactly the prescribed number of ambient slots
owned by each block, including empty blocks. -/
theorem FamilySlotShuffleTo.card_ownerFiber
    {ι : Type*} {size : ι → ℕ} {total : ℕ}
    (σ : FamilySlotShuffleTo size total) (i : ι) :
    Fintype.card {v : Fin total // (σ.slotEquiv.symm v).1 = i} = size i := by
  classical
  let f : Fin (size i) →
      {v : Fin total // (σ.slotEquiv.symm v).1 = i} :=
    fun j => ⟨σ.slotEquiv ⟨i, j⟩, by simp⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h := σ.slotEquiv.injective (congrArg Subtype.val hab)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rcases hslot : σ.slotEquiv.symm v with ⟨i', j⟩
    have hi : i' = i := by simpa [hslot] using hv
    subst i'
    refine ⟨j, ?_⟩
    apply Subtype.ext
    dsimp [f]
    calc
      σ.slotEquiv ⟨i, j⟩ =
          σ.slotEquiv (σ.slotEquiv.symm v) :=
        congrArg σ.slotEquiv hslot.symm
      _ = v := σ.slotEquiv.apply_symm_apply v
  simpa using (Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

open Classical in
/-- Construct the unique order-preserving shuffle of a fixed prescribed
local size from an owner assignment with those fiber cardinalities. -/
@[nolint unusedArguments]
noncomputable def assignmentShuffleOfSize
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (owner : Fin total → ι)
    (hcard : ∀ i, Fintype.card {v : Fin total // owner v = i} = size i) :
    FamilySlotShuffleTo size total :=
  (familyOrderDecompositionEquivOfSize
    (fun i : ι => {v : Fin total // owner v = i})
    size hcard (Equiv.sigmaFiberEquiv owner).symm
    (Equiv.refl (Fin total))).2

open Classical in
/-- Each assigned local shuffle slot still belongs to its original
owner block. -/
theorem assignmentShuffleOfSize_apply_owner
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (owner : Fin total → ι)
    (hcard : ∀ i, Fintype.card {v : Fin total // owner v = i} = size i)
    (i : ι) (j : Fin (size i)) :
    owner ((assignmentShuffleOfSize owner hcard).slotEquiv ⟨i, j⟩) = i := by
  classical
  let orders :=
    familyOrdersOfOrder
      (fun i : ι => {v : Fin total // owner v = i})
      size hcard (Equiv.sigmaFiberEquiv owner).symm
      (Equiv.refl (Fin total))
  have h := (orders i j).property
  change owner ((orders i j).1) = i
  exact h

open Classical in
/-- Unshuffling the fixed-size owner assignment recovers its original
block name pointwise. -/
theorem assignmentShuffleOfSize_symm_owner
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (owner : Fin total → ι)
    (hcard : ∀ i, Fintype.card {v : Fin total // owner v = i} = size i)
    (v : Fin total) :
    ((assignmentShuffleOfSize owner hcard).slotEquiv.symm v).1 = owner v := by
  classical
  let σ := assignmentShuffleOfSize owner hcard
  rcases hslot : σ.slotEquiv.symm v with ⟨i, j⟩
  have hback : σ.slotEquiv ⟨i, j⟩ = v := by
    calc
      σ.slotEquiv ⟨i, j⟩ =
          σ.slotEquiv (σ.slotEquiv.symm v) :=
        congrArg σ.slotEquiv hslot.symm
      _ = v := σ.slotEquiv.apply_symm_apply v
  simpa [σ, hback] using
    (assignmentShuffleOfSize_apply_owner owner hcard i j).symm

open Classical in
/-- At fixed block sizes, assignments of all ambient slots to named
blocks, each with exactly its prescribed size, are equivalent to
order-preserving family shuffles. This includes empty blocks. -/
noncomputable def familyShuffleOwnerEquiv
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ} :
    FamilySlotShuffleTo size total ≃
      {owner : Fin total → ι //
        ∀ i, Fintype.card {v : Fin total // owner v = i} = size i} where
  toFun σ :=
    ⟨fun v => (σ.slotEquiv.symm v).1, fun i => σ.card_ownerFiber i⟩
  invFun o := assignmentShuffleOfSize o.1 o.2
  left_inv σ := by
    apply FamilySlotShuffleTo.eq_of_same_owner
    intro v
    exact (assignmentShuffleOfSize_symm_owner
      (fun v => (σ.slotEquiv.symm v).1)
      (fun i => σ.card_ownerFiber i) v)
  right_inv o := by
    apply Subtype.ext
    funext v
    exact assignmentShuffleOfSize_symm_owner o.1 o.2 v

open Classical in
/-- Canonical finite enumeration of fixed-size owner assignments.
Keeping the finite set explicit avoids selecting an unrelated subtype
enumeration in the type of a theorem about weighted sums. -/
noncomputable def fixedSizeOwnerFiniteDomain
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ} :
    Finset {owner : Fin total → ι //
      ∀ i, Fintype.card {v : Fin total // owner v = i} = size i} :=
  (Finset.univ : Finset (FamilySlotShuffleTo size total)).image
    (familyShuffleOwnerEquiv (ι := ι) (size := size) (total := total))

/-- Reindex an arbitrary weighted family-shuffle sum by assignments
with the same fixed local cardinalities. In particular, this counts
no spurious permutations of the slots inside a block. -/
theorem sum_familyShuffles_eq_sum_fixedSizeOwners
    {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    {size : ι → ℕ} {total : ℕ}
    (weight : FamilySlotShuffleTo size total → M) :
    (∑ σ : FamilySlotShuffleTo size total, weight σ) =
      ∑ o ∈ fixedSizeOwnerFiniteDomain (ι := ι) (size := size) (total := total),
        weight (familyShuffleOwnerEquiv.symm o) := by
  classical
  unfold fixedSizeOwnerFiniteDomain
  rw [Finset.sum_image]
  · simp
  · intro x _ y _ h
    exact (familyShuffleOwnerEquiv (ι := ι) (size := size)
      (total := total)).injective h

end Combinatorics
