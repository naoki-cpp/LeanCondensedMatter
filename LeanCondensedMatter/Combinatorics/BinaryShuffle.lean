import Mathlib

set_option linter.style.header false

/-!
# Binary order-preserving shuffles

`BinaryShuffle m n` records an interleaving of `m` left slots and `n` right slots while preserving
both internal orders. Constructors add the outermost slot, matching the recursive structure used by
ordered-simplex shuffle integrals.
-/

namespace Combinatorics

/-- An order-preserving interleaving of `m` left slots and `n` right slots.

The constructors add the outermost slot. Thus a positive-dimensional shuffle is uniquely classified
by whether its outermost slot comes from the left or the right input. -/
inductive BinaryShuffle : ℕ → ℕ → Type
  | nil : BinaryShuffle 0 0
  | consLeft {m n : ℕ} : BinaryShuffle m n → BinaryShuffle (m + 1) n
  | consRight {m n : ℕ} : BinaryShuffle m n → BinaryShuffle m (n + 1)
  deriving DecidableEq

namespace BinaryShuffle

/-- The unique shuffle with no left slots. -/
def allRight : (n : ℕ) → BinaryShuffle 0 n
  | 0 => .nil
  | n + 1 => .consRight (allRight n)

/-- The unique shuffle with no right slots. -/
def allLeft : (m : ℕ) → BinaryShuffle m 0
  | 0 => .nil
  | m + 1 => .consLeft (allLeft m)

/-- Every shuffle with no left slots is the all-right shuffle. -/
theorem eq_allRight : ∀ {n : ℕ} (σ : BinaryShuffle 0 n), σ = allRight n
  | 0, .nil => rfl
  | _ + 1, .consRight σ => congrArg consRight (eq_allRight σ)

/-- Every shuffle with no right slots is the all-left shuffle. -/
theorem eq_allLeft : ∀ {m : ℕ} (σ : BinaryShuffle m 0), σ = allLeft m
  | 0, .nil => rfl
  | _ + 1, .consLeft σ => congrArg consLeft (eq_allLeft σ)

/-- Shuffles with no left slots form a singleton type. -/
def zeroLeftEquiv (n : ℕ) : BinaryShuffle 0 n ≃ Unit where
  toFun _ := ()
  invFun _ := allRight n
  left_inv σ := (eq_allRight σ).symm
  right_inv _ := rfl

/-- Shuffles with no right slots form a singleton type. -/
def zeroRightEquiv (m : ℕ) : BinaryShuffle m 0 ≃ Unit where
  toFun _ := ()
  invFun _ := allLeft m
  left_inv σ := (eq_allLeft σ).symm
  right_inv _ := rfl

/-- A positive-dimensional binary shuffle is classified by the side of its outermost slot. -/
def outerEquiv (m n : ℕ) :
    BinaryShuffle (m + 1) (n + 1) ≃
      BinaryShuffle m (n + 1) ⊕ BinaryShuffle (m + 1) n where
  toFun
    | .consLeft σ => Sum.inl σ
    | .consRight σ => Sum.inr σ
  invFun
    | Sum.inl σ => .consLeft σ
    | Sum.inr σ => .consRight σ
  left_inv := by
    intro σ
    cases σ <;> rfl
  right_inv := by
    intro σ
    cases σ <;> rfl

/-- Binary shuffles form a finite type. -/
@[reducible]
noncomputable def fintype : ∀ (m n : ℕ), Fintype (BinaryShuffle m n)
  | 0, n => Fintype.ofEquiv Unit (zeroLeftEquiv n).symm
  | m + 1, 0 => Fintype.ofEquiv Unit (zeroRightEquiv (m + 1)).symm
  | m + 1, n + 1 =>
      letI : Fintype (BinaryShuffle m (n + 1)) := fintype m (n + 1)
      letI : Fintype (BinaryShuffle (m + 1) n) := fintype (m + 1) n
      Fintype.ofEquiv
        (BinaryShuffle m (n + 1) ⊕ BinaryShuffle (m + 1) n)
        (outerEquiv m n).symm
termination_by m n => m + n

noncomputable instance instFintype (m n : ℕ) : Fintype (BinaryShuffle m n) :=
  fintype m n

@[simp]
theorem card_zero_left (n : ℕ) : Fintype.card (BinaryShuffle 0 n) = 1 := by
  rw [Fintype.card_congr (zeroLeftEquiv n)]
  simp

@[simp]
theorem card_zero_right (m : ℕ) : Fintype.card (BinaryShuffle m 0) = 1 := by
  rw [Fintype.card_congr (zeroRightEquiv m)]
  simp

/-- Pascal recursion for the number of binary shuffles. -/
theorem card_succ_succ (m n : ℕ) :
    Fintype.card (BinaryShuffle (m + 1) (n + 1)) =
      Fintype.card (BinaryShuffle m (n + 1)) +
        Fintype.card (BinaryShuffle (m + 1) n) := by
  rw [Fintype.card_congr (outerEquiv m n)]
  simp

/-- A finite sum over shuffles with no left slots has one term. -/
theorem sum_zero_left [AddCommMonoid M] (n : ℕ) (F : BinaryShuffle 0 n → M) :
    ∑ σ : BinaryShuffle 0 n, F σ = F (allRight n) := by
  simpa [zeroLeftEquiv] using (Equiv.sum_comp (zeroLeftEquiv n).symm F).symm

/-- A finite sum over shuffles with no right slots has one term. -/
theorem sum_zero_right [AddCommMonoid M] (m : ℕ) (F : BinaryShuffle m 0 → M) :
    ∑ σ : BinaryShuffle m 0, F σ = F (allLeft m) := by
  simpa [zeroRightEquiv] using (Equiv.sum_comp (zeroRightEquiv m).symm F).symm

/-- Split a finite shuffle sum by the side that supplies the outermost slot. -/
theorem sum_succ_succ [AddCommMonoid M] (m n : ℕ)
    (F : BinaryShuffle (m + 1) (n + 1) → M) :
    ∑ σ : BinaryShuffle (m + 1) (n + 1), F σ =
      (∑ σ : BinaryShuffle m (n + 1), F (.consLeft σ)) +
        ∑ σ : BinaryShuffle (m + 1) n, F (.consRight σ) := by
  simpa [outerEquiv] using (Equiv.sum_comp (outerEquiv m n).symm F).symm

end BinaryShuffle
end Combinatorics
