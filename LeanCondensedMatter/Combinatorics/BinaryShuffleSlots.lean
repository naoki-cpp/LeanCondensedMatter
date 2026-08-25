import LeanCondensedMatter.Combinatorics.BinaryShuffle
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Ambient slots of binary shuffles

A `BinaryShuffle m n` records only the recursive left/right choices. This module extracts the
corresponding ambient positions of every left and right local slot, proves that both embeddings are
strictly increasing and have disjoint ranges, and packages their union as an equivalence
`Fin m ⊕ Fin n ≃ Fin (m + n)`.
-/

namespace Combinatorics
namespace BinaryShuffle

/-- Ambient position of a left local slot. -/
def leftSlot : {m n : ℕ} → BinaryShuffle m n → Fin m → Fin (m + n)
  | 0, 0, .nil => Fin.elim0
  | m + 1, n, .consLeft σ => fun i =>
      Fin.cases 0 (fun j => Fin.cast (by lia) (leftSlot σ j).succ) i
  | m, n + 1, .consRight σ => fun i =>
      Fin.cast (by lia) (leftSlot σ i).succ

/-- Ambient position of a right local slot. -/
def rightSlot : {m n : ℕ} → BinaryShuffle m n → Fin n → Fin (m + n)
  | 0, 0, .nil => Fin.elim0
  | m + 1, n, .consLeft σ => fun j =>
      Fin.cast (by lia) (rightSlot σ j).succ
  | m, n + 1, .consRight σ => fun j =>
      Fin.cases 0 (fun k => Fin.cast (by lia) (rightSlot σ k).succ) j

@[simp]
theorem leftSlot_consLeft_zero {m n : ℕ} (σ : BinaryShuffle m n) :
    leftSlot (.consLeft σ) 0 = 0 := rfl

@[simp]
theorem leftSlot_consLeft_succ {m n : ℕ} (σ : BinaryShuffle m n) (i : Fin m) :
    leftSlot (.consLeft σ) i.succ = Fin.cast (by lia) (leftSlot σ i).succ := rfl

@[simp]
theorem rightSlot_consLeft {m n : ℕ} (σ : BinaryShuffle m n) (j : Fin n) :
    rightSlot (.consLeft σ) j = Fin.cast (by lia) (rightSlot σ j).succ := rfl

@[simp]
theorem leftSlot_consRight {m n : ℕ} (σ : BinaryShuffle m n) (i : Fin m) :
    leftSlot (.consRight σ) i = Fin.cast (by lia) (leftSlot σ i).succ := by
  simp [leftSlot]

@[simp]
theorem rightSlot_consRight_zero {m n : ℕ} (σ : BinaryShuffle m n) :
    rightSlot (.consRight σ) 0 = 0 := by
  simp [rightSlot]

@[simp]
theorem rightSlot_consRight_succ {m n : ℕ} (σ : BinaryShuffle m n) (j : Fin n) :
    rightSlot (.consRight σ) j.succ = Fin.cast (by lia) (rightSlot σ j).succ := by
  simp [rightSlot]

/-- Left local slots retain their internal order in ambient coordinates. -/
theorem leftSlot_strictMono : ∀ {m n : ℕ} (σ : BinaryShuffle m n), StrictMono (leftSlot σ)
  | 0, 0, .nil => fun i => Fin.elim0 i
  | m + 1, n, .consLeft σ => by
      intro i j hij
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              simp only [leftSlot_consLeft_zero, leftSlot_consLeft_succ]
              change 0 < (leftSlot σ j).val + 1
              lia
      | succ i =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              have hbase : i < j := by simpa using hij
              have h := leftSlot_strictMono σ hbase
              simp only [leftSlot_consLeft_succ]
              change (leftSlot σ i).val + 1 < (leftSlot σ j).val + 1
              lia
  | m, n + 1, .consRight σ => by
      intro i j hij
      have h := leftSlot_strictMono σ hij
      simp only [leftSlot_consRight]
      change (leftSlot σ i).val + 1 < (leftSlot σ j).val + 1
      lia

/-- Right local slots retain their internal order in ambient coordinates. -/
theorem rightSlot_strictMono : ∀ {m n : ℕ} (σ : BinaryShuffle m n), StrictMono (rightSlot σ)
  | 0, 0, .nil => fun i => Fin.elim0 i
  | m + 1, n, .consLeft σ => by
      intro i j hij
      have h := rightSlot_strictMono σ hij
      simp only [rightSlot_consLeft]
      change (rightSlot σ i).val + 1 < (rightSlot σ j).val + 1
      lia
  | m, n + 1, .consRight σ => by
      intro i j hij
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              simp only [rightSlot_consRight_zero, rightSlot_consRight_succ]
              change 0 < (rightSlot σ j).val + 1
              lia
      | succ i =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              have hbase : i < j := by simpa using hij
              have h := rightSlot_strictMono σ hbase
              simp only [rightSlot_consRight_succ]
              change (rightSlot σ i).val + 1 < (rightSlot σ j).val + 1
              lia

/-- A left and a right local slot never occupy the same ambient position. -/
theorem leftSlot_ne_rightSlot : ∀ {m n : ℕ} (σ : BinaryShuffle m n)
    (i : Fin m) (j : Fin n), leftSlot σ i ≠ rightSlot σ j
  | 0, 0, .nil, i, _j => Fin.elim0 i
  | m + 1, n, .consLeft σ, i, j => by
      induction i using Fin.cases with
      | zero =>
          intro h
          have hv := congrArg Fin.val h
          simp only [leftSlot_consLeft_zero, rightSlot_consLeft, Fin.val_cast, Fin.val_succ,
            Fin.val_zero] at hv
          lia
      | succ i =>
          intro h
          apply leftSlot_ne_rightSlot σ i j
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [leftSlot_consLeft_succ, rightSlot_consLeft, Fin.val_cast, Fin.val_succ] at hv
          lia
  | m, n + 1, .consRight σ, i, j => by
      induction j using Fin.cases with
      | zero =>
          intro h
          have hv := congrArg Fin.val h
          simp only [leftSlot_consRight, rightSlot_consRight_zero, Fin.val_cast, Fin.val_succ,
            Fin.val_zero] at hv
          lia
      | succ j =>
          intro h
          apply leftSlot_ne_rightSlot σ i j
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [leftSlot_consRight, rightSlot_consRight_succ, Fin.val_cast, Fin.val_succ] at hv
          lia

/-- Ambient slot occupied by a tagged left or right local slot. -/
def slot {m n : ℕ} (σ : BinaryShuffle m n) : Fin m ⊕ Fin n → Fin (m + n)
  | Sum.inl i => leftSlot σ i
  | Sum.inr j => rightSlot σ j

/-- The tagged-slot map of a binary shuffle is injective. -/
theorem slot_injective {m n : ℕ} (σ : BinaryShuffle m n) : Function.Injective (slot σ) := by
  intro x y h
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          cases (leftSlot_strictMono σ).injective h
          rfl
      | inr j =>
          exact (leftSlot_ne_rightSlot σ i j h).elim
  | inr i =>
      cases y with
      | inl j =>
          exact (leftSlot_ne_rightSlot σ j i h.symm).elim
      | inr j =>
          cases (rightSlot_strictMono σ).injective h
          rfl

/-- The tagged local slots are equivalent to all ambient slots. -/
noncomputable def slotEquiv {m n : ℕ} (σ : BinaryShuffle m n) :
    Fin m ⊕ Fin n ≃ Fin (m + n) :=
  Equiv.ofBijective (slot σ)
    ((Fintype.bijective_iff_injective_and_card (slot σ)).2 ⟨slot_injective σ, by simp⟩)

@[simp]
theorem slotEquiv_inl {m n : ℕ} (σ : BinaryShuffle m n) (i : Fin m) :
    slotEquiv σ (Sum.inl i) = leftSlot σ i := rfl

@[simp]
theorem slotEquiv_inr {m n : ℕ} (σ : BinaryShuffle m n) (j : Fin n) :
    slotEquiv σ (Sum.inr j) = rightSlot σ j := rfl

/-- An order-preserving equivalence of two local slot families with the ambient slots. -/
structure SlotShuffle (m n : ℕ) where
  /-- Equivalence between tagged local slots and ambient slots. -/
  slotEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)
  strictMonoLeft : StrictMono (fun i => slotEquiv (Sum.inl i))
  strictMonoRight : StrictMono (fun j => slotEquiv (Sum.inr j))

/-- Forget the recursive presentation and retain only the ambient slot equivalence. -/
noncomputable def toSlotShuffle {m n : ℕ} (σ : BinaryShuffle m n) : SlotShuffle m n where
  slotEquiv := slotEquiv σ
  strictMonoLeft := by simpa using leftSlot_strictMono σ
  strictMonoRight := by simpa using rightSlot_strictMono σ

end BinaryShuffle
end Combinatorics