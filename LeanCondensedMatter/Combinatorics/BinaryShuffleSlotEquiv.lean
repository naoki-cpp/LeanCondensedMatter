import LeanCondensedMatter.Combinatorics.BinaryShuffleSlots

set_option linter.style.header false

/-!
# Recursive binary shuffles as an adapter to ambient slot shuffles

The recursive and ambient presentations encode the same order-preserving interleavings. The
forgetful map is injective by recursion; its surjectivity follows from the independent binomial
cardinality of ambient left-slot sets.
-/

namespace Combinatorics

open scoped BigOperators
namespace BinaryShuffle

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

/-- Recursive binary shuffles are counted by the same binomial coefficient. -/
theorem card_eq_choose : ∀ (m n : ℕ),
    Fintype.card (BinaryShuffle m n) = Nat.choose (m + n) m
  | 0, n => by simp
  | m + 1, 0 => by simp
  | m + 1, n + 1 => by
      rw [card_succ_succ, card_eq_choose m (n + 1), card_eq_choose (m + 1) n]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ' (m + n + 1) m).symm

/-- Recursive binary shuffles are equivalent to order-preserving ambient slot shuffles. -/
noncomputable def slotShuffleEquiv (m n : ℕ) :
    BinaryShuffle m n ≃ SlotShuffle m n :=
  Equiv.ofBijective (fun σ : BinaryShuffle m n => toSlotShuffle σ)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨toSlotShuffle_injective, by rw [card_eq_choose, SlotShuffle.card_eq_choose]⟩)

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
