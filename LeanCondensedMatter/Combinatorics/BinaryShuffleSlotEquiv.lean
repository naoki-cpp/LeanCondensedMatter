import LeanCondensedMatter.Combinatorics.BinaryShuffleSlots
import LeanCondensedMatter.Combinatorics.SumEquivPartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Recursive binary shuffles and ambient slot shuffles

`BinaryShuffle m n` and `BinaryShuffle.SlotShuffle m n` encode the same order-preserving
interleavings in two different ways.  This module proves that the forgetful map from the recursive
presentation to the ambient-slot presentation is an equivalence.

The proof avoids a dependent recursive construction that deletes the first ambient slot.  Instead,
both presentations inject into the type of `m`-element subsets of `Fin (m + n)`: a slot shuffle is
uniquely determined by the ambient positions occupied by its left family, and both types have the
binomial cardinality `(m + n).choose m`.
-/

namespace Combinatorics
namespace BinaryShuffle

/-- Two ambient slot shuffles are equal when their slot equivalences are equal. -/
@[ext]
theorem SlotShuffle.ext {m n : ℕ} {σ τ : SlotShuffle m n}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Ambient slot shuffles form a finite type. -/
noncomputable instance SlotShuffle.instFintype (m n : ℕ) : Fintype (SlotShuffle m n) :=
  Fintype.ofInjective (fun σ : SlotShuffle m n => σ.slotEquiv)
    (fun _ _ h => SlotShuffle.ext h)

/-- The ambient slot equivalence determines the recursive binary shuffle. -/
theorem slotEquiv_injective :
    ∀ {m n : ℕ} (σ τ : BinaryShuffle m n), slotEquiv σ = slotEquiv τ → σ = τ
  | 0, 0, .nil, .nil, _ => rfl
  | m + 1, n, .consLeft σ, .consLeft τ, h => by
      congr 1
      apply slotEquiv_injective σ τ
      apply Equiv.ext
      intro x
      cases x with
      | inl i =>
          apply Fin.ext
          change (leftSlot σ i).val = (leftSlot τ i).val
          have hx := congrArg (fun e => e (Sum.inl i.succ)) h
          have hxv := congrArg Fin.val hx
          simp only [slotEquiv_inl, leftSlot_consLeft_succ, Fin.val_cast, Fin.val_succ] at hxv
          lia
      | inr j =>
          apply Fin.ext
          change (rightSlot σ j).val = (rightSlot τ j).val
          have hx := congrArg (fun e => e (Sum.inr j)) h
          have hxv := congrArg Fin.val hx
          simp only [slotEquiv_inr, rightSlot_consLeft, Fin.val_cast, Fin.val_succ] at hxv
          lia
  | m + 1, n + 1, .consLeft σ, .consRight τ, h => by
      exfalso
      have hx := congrArg (fun e => e (Sum.inl (0 : Fin (m + 1)))) h
      have hxv := congrArg Fin.val hx
      simp only [slotEquiv_inl, leftSlot_consLeft_zero, leftSlot_consRight, Fin.val_zero,
        Fin.val_cast, Fin.val_succ] at hxv
      lia
  | m, n + 1, .consRight σ, .consRight τ, h => by
      congr 1
      apply slotEquiv_injective σ τ
      apply Equiv.ext
      intro x
      cases x with
      | inl i =>
          apply Fin.ext
          change (leftSlot σ i).val = (leftSlot τ i).val
          have hx := congrArg (fun e => e (Sum.inl i)) h
          have hxv := congrArg Fin.val hx
          simp only [slotEquiv_inl, leftSlot_consRight, Fin.val_cast, Fin.val_succ] at hxv
          lia
      | inr j =>
          apply Fin.ext
          change (rightSlot σ j).val = (rightSlot τ j).val
          have hx := congrArg (fun e => e (Sum.inr j.succ)) h
          have hxv := congrArg Fin.val hx
          simp only [slotEquiv_inr, rightSlot_consRight_succ, Fin.val_cast, Fin.val_succ] at hxv
          lia
  | m + 1, n + 1, .consRight σ, .consLeft τ, h => by
      exfalso
      have hx := congrArg (fun e => e (Sum.inl (0 : Fin (m + 1)))) h
      have hxv := congrArg Fin.val hx
      simp only [slotEquiv_inl, leftSlot_consRight, leftSlot_consLeft_zero, Fin.val_zero,
        Fin.val_cast, Fin.val_succ] at hxv
      lia

/-- Forgetting the recursive presentation is injective. -/
theorem toSlotShuffle_injective {m n : ℕ} :
    Function.Injective (toSlotShuffle : BinaryShuffle m n → SlotShuffle m n) := by
  intro σ τ h
  apply slotEquiv_injective σ τ
  exact congrArg SlotShuffle.slotEquiv h

/-- Ambient positions occupied by the left local slots. -/
def SlotShuffle.leftSlots {m n : ℕ} (σ : SlotShuffle m n) : Finset (Fin (m + n)) :=
  SumEquiv.leftImage σ.slotEquiv

/-- Ambient positions occupied by the right local slots. -/
def SlotShuffle.rightSlots {m n : ℕ} (σ : SlotShuffle m n) : Finset (Fin (m + n)) :=
  SumEquiv.rightImage σ.slotEquiv

@[simp]
theorem SlotShuffle.card_leftSlots {m n : ℕ} (σ : SlotShuffle m n) :
    σ.leftSlots.card = m := by
  simpa [SlotShuffle.leftSlots] using (SumEquiv.card_leftImage σ.slotEquiv)

@[simp]
theorem SlotShuffle.card_rightSlots {m n : ℕ} (σ : SlotShuffle m n) :
    σ.rightSlots.card = n := by
  simpa [SlotShuffle.rightSlots] using (SumEquiv.card_rightImage σ.slotEquiv)

@[simp]
theorem SlotShuffle.mem_leftSlots_iff {m n : ℕ} (σ : SlotShuffle m n)
    (x : Fin (m + n)) :
    x ∈ σ.leftSlots ↔ ∃ i : Fin m, σ.slotEquiv (Sum.inl i) = x := by
  simpa [SlotShuffle.leftSlots] using (SumEquiv.mem_leftImage_iff σ.slotEquiv x)

@[simp]
theorem SlotShuffle.mem_rightSlots_iff {m n : ℕ} (σ : SlotShuffle m n)
    (x : Fin (m + n)) :
    x ∈ σ.rightSlots ↔ ∃ j : Fin n, σ.slotEquiv (Sum.inr j) = x := by
  simpa [SlotShuffle.rightSlots] using (SumEquiv.mem_rightImage_iff σ.slotEquiv x)

/-- The right slots are precisely the complement of the left slots. -/
theorem SlotShuffle.mem_rightSlots_iff_not_mem_leftSlots {m n : ℕ}
    (σ : SlotShuffle m n) (x : Fin (m + n)) :
    x ∈ σ.rightSlots ↔ x ∉ σ.leftSlots := by
  simpa [SlotShuffle.leftSlots, SlotShuffle.rightSlots] using
    (SumEquiv.mem_rightImage_iff_not_mem_leftImage σ.slotEquiv x)

/-- The complement of the left slots has the right perturbation order. -/
@[simp]
theorem SlotShuffle.card_sdiff_leftSlots {m n : ℕ} (σ : SlotShuffle m n) :
    ((Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots).card = n := by
  have hright :
      (Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots = σ.rightSlots := by
    simpa [SlotShuffle.leftSlots, SlotShuffle.rightSlots] using
      (SumEquiv.rightImage_eq_sdiff_leftImage σ.slotEquiv).symm
  rw [hright, σ.card_rightSlots]

/-- The increasing enumeration of the complement of the left slots is the right slot map. -/
theorem SlotShuffle.sdiffLeftSlots_orderEmbOfFin {m n : ℕ}
    (σ : SlotShuffle m n) (j : Fin n) :
    ((Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots).orderEmbOfFin
        σ.card_sdiff_leftSlots j =
      σ.slotEquiv (Sum.inr j) := by
  have h := Finset.orderEmbOfFin_unique
    (s := (Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots)
    (h := σ.card_sdiff_leftSlots)
    (f := fun q => σ.slotEquiv (Sum.inr q))
    (fun q => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact (σ.mem_rightSlots_iff_not_mem_leftSlots _).1
        ((σ.mem_rightSlots_iff _).2 ⟨q, rfl⟩))
    σ.strictMonoRight
  exact congrFun h.symm j

/-- A slot shuffle is uniquely determined by the ambient positions of its left slots. -/
theorem SlotShuffle.eq_of_leftSlots_eq {m n : ℕ} {σ τ : SlotShuffle m n}
    (hslots : σ.leftSlots = τ.leftSlots) : σ = τ := by
  apply SlotShuffle.ext
  apply Equiv.ext
  intro x
  cases x with
  | inl i =>
      have hσ := Finset.orderEmbOfFin_unique
        (s := σ.leftSlots) (h := σ.card_leftSlots)
        (f := fun k => σ.slotEquiv (Sum.inl k))
        (fun k => (σ.mem_leftSlots_iff _).2 ⟨k, rfl⟩) σ.strictMonoLeft
      have hτ := Finset.orderEmbOfFin_unique
        (s := σ.leftSlots) (h := σ.card_leftSlots)
        (f := fun k => τ.slotEquiv (Sum.inl k))
        (fun k => by
          rw [hslots]
          exact (τ.mem_leftSlots_iff _).2 ⟨k, rfl⟩) τ.strictMonoLeft
      exact congrFun (hσ.trans hτ.symm) i
  | inr j =>
      have hright : σ.rightSlots = τ.rightSlots := by
        ext x
        rw [σ.mem_rightSlots_iff_not_mem_leftSlots,
          τ.mem_rightSlots_iff_not_mem_leftSlots, hslots]
      have hσ := Finset.orderEmbOfFin_unique
        (s := σ.rightSlots) (h := σ.card_rightSlots)
        (f := fun k => σ.slotEquiv (Sum.inr k))
        (fun k => (σ.mem_rightSlots_iff _).2 ⟨k, rfl⟩) σ.strictMonoRight
      have hτ := Finset.orderEmbOfFin_unique
        (s := σ.rightSlots) (h := σ.card_rightSlots)
        (f := fun k => τ.slotEquiv (Sum.inr k))
        (fun k => by
          rw [hright]
          exact (τ.mem_rightSlots_iff _).2 ⟨k, rfl⟩) τ.strictMonoRight
      exact congrFun (hσ.trans hτ.symm) j

/-- The type of possible ambient left-slot sets. -/
abbrev LeftSlotSet (m n : ℕ) :=
  {s : Finset (Fin (m + n)) // s.card = m}

/-- Record only the ambient set occupied by the left family. -/
def SlotShuffle.toLeftSlotSet {m n : ℕ} (σ : SlotShuffle m n) : LeftSlotSet m n :=
  ⟨σ.leftSlots, σ.card_leftSlots⟩

/-- The left-slot set determines the whole slot shuffle. -/
theorem SlotShuffle.toLeftSlotSet_injective {m n : ℕ} :
    Function.Injective (SlotShuffle.toLeftSlotSet : SlotShuffle m n → LeftSlotSet m n) := by
  intro σ τ h
  apply SlotShuffle.eq_of_leftSlots_eq
  exact congrArg Subtype.val h

/-- The possible left-slot sets are counted by a binomial coefficient. -/
theorem card_leftSlotSet (m n : ℕ) :
    Fintype.card (LeftSlotSet m n) = Nat.choose (m + n) m := by
  classical
  change Fintype.card {s : Finset (Fin (m + n)) // s.card = m} = Nat.choose (m + n) m
  let e : {s : Finset (Fin (m + n)) // s.card = m} ≃
      ↥((Finset.univ : Finset (Fin (m + n))).powersetCard m) :=
    { toFun := fun s : {s : Finset (Fin (m + n)) // s.card = m} =>
        ⟨s.1, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, s.2⟩⟩
      invFun := fun s : ↥((Finset.univ : Finset (Fin (m + n))).powersetCard m) =>
        ⟨s.1, (Finset.mem_powersetCard.1 s.2).2⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  rw [Fintype.card_congr e]
  simp

/-- Recursive binary shuffles are counted by the same binomial coefficient. -/
theorem card_eq_choose : ∀ (m n : ℕ),
    Fintype.card (BinaryShuffle m n) = Nat.choose (m + n) m
  | 0, n => by simp
  | m + 1, 0 => by simp
  | m + 1, n + 1 => by
      rw [card_succ_succ, card_eq_choose m (n + 1), card_eq_choose (m + 1) n]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ' (m + n + 1) m).symm

/-- Ambient slot shuffles have the binomial cardinality. -/
theorem card_slotShuffle (m n : ℕ) :
    Fintype.card (SlotShuffle m n) = Nat.choose (m + n) m := by
  have hlower : Fintype.card (BinaryShuffle m n) ≤ Fintype.card (SlotShuffle m n) :=
    Fintype.card_le_of_injective
      (fun σ : BinaryShuffle m n => toSlotShuffle σ) toSlotShuffle_injective
  have hupper : Fintype.card (SlotShuffle m n) ≤ Fintype.card (LeftSlotSet m n) :=
    Fintype.card_le_of_injective
      (fun σ : SlotShuffle m n => σ.toLeftSlotSet) SlotShuffle.toLeftSlotSet_injective
  rw [card_eq_choose] at hlower
  rw [card_leftSlotSet] at hupper
  lia

/-- Ambient slot shuffles are equivalent to their ambient left-slot sets. -/
noncomputable def slotShuffleLeftSlotSetEquiv (m n : ℕ) :
    SlotShuffle m n ≃ LeftSlotSet m n :=
  Equiv.ofBijective SlotShuffle.toLeftSlotSet
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨SlotShuffle.toLeftSlotSet_injective, by rw [card_slotShuffle, card_leftSlotSet]⟩)

@[simp]
theorem slotShuffleLeftSlotSetEquiv_apply {m n : ℕ} (σ : SlotShuffle m n) :
    slotShuffleLeftSlotSetEquiv m n σ = σ.toLeftSlotSet := rfl

/-- Reindex a finite sum over left-slot sets by ambient slot shuffles. -/
theorem sum_leftSlotSet [AddCommMonoid M] (m n : ℕ) (F : LeftSlotSet m n → M) :
    ∑ s : LeftSlotSet m n, F s =
      ∑ σ : SlotShuffle m n, F σ.toLeftSlotSet := by
  simpa using (Equiv.sum_comp (slotShuffleLeftSlotSetEquiv m n) F).symm

/-- Recursive binary shuffles are equivalent to order-preserving ambient slot shuffles. -/
noncomputable def slotShuffleEquiv (m n : ℕ) :
    BinaryShuffle m n ≃ SlotShuffle m n :=
  Equiv.ofBijective (fun σ : BinaryShuffle m n => toSlotShuffle σ)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨toSlotShuffle_injective, by rw [card_eq_choose, card_slotShuffle]⟩)

@[simp]
theorem slotShuffleEquiv_apply {m n : ℕ} (σ : BinaryShuffle m n) :
    slotShuffleEquiv m n σ = toSlotShuffle σ := rfl

/-- Reindex a finite sum over ambient slot shuffles by recursive binary shuffles. -/
theorem sum_slotShuffle [AddCommMonoid M] (m n : ℕ) (F : SlotShuffle m n → M) :
    ∑ shuffle : SlotShuffle m n, F shuffle =
      ∑ σ : BinaryShuffle m n, F (toSlotShuffle σ) := by
  simpa using (Equiv.sum_comp (slotShuffleEquiv m n) F).symm

end BinaryShuffle
end Combinatorics