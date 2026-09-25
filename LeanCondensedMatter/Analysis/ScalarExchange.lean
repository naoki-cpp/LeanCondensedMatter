import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scalar exchange algebra

This module owns the representation-independent algebra behind fixed-sign exchange relations.

For an associative unital complex algebra, the fixed-sign bracket is

```text
[A,B]_ζ = A B - ζ B A.
```

The same scalar exchange relation also drives the finite peel identity used by bosonic and
fermionic operator realizations. Concrete endomorphism APIs may specialize this algebra without
owning a second copy of the exchange identities.
-/

namespace ScalarExchange

/-- The fixed-sign bracket `[A,B]_ζ = A B - ζ B A` in an associative complex algebra. -/
noncomputable def zetaCommutator {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ : ℂ) (a b : A) : A :=
  a * b - ζ • (b * a)

/-- Additivity in the left argument. -/
theorem zetaCommutator_add_left {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ : ℂ) (a b c : A) :
    zetaCommutator ζ (a + b) c =
      zetaCommutator ζ a c + zetaCommutator ζ b c := by
  simp only [zetaCommutator, add_mul, mul_add, smul_add]
  module

/-- Additivity in the right argument. -/
theorem zetaCommutator_add_right {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ : ℂ) (a b c : A) :
    zetaCommutator ζ a (b + c) =
      zetaCommutator ζ a b + zetaCommutator ζ a c := by
  simp only [zetaCommutator, add_mul, mul_add, smul_add]
  module

/-- Scalar multiples factor out of both arguments. -/
theorem zetaCommutator_smul_smul {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ c d : ℂ) (a b : A) :
    zetaCommutator ζ (c • a) (d • b) = (c * d) • zetaCommutator ζ a b := by
  simp only [zetaCommutator, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  module

/-- Reorder a product from a supplied fixed-sign bracket value. -/
theorem mul_eq_add_smul_mul_of_zetaCommutator_eq
    {A : Type*} [Ring A] [Algebra ℂ A] (ζ : ℂ) {a b c : A}
    (h : zetaCommutator ζ a b = c) :
    a * b = c + ζ • (b * a) := by
  have h' : a * b - ζ • (b * a) = c := by
    simpa [zetaCommutator] using h
  exact (sub_eq_iff_eq_add).mp h'

/-- Reversal for an involutive exchange scalar. -/
theorem zetaCommutator_swap_of_sq_eq_one
    {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ : ℂ) (hζ : ζ * ζ = 1) (a b : A) :
    zetaCommutator ζ b a = (-ζ) • zetaCommutator ζ a b := by
  have hneg : (-ζ) * ζ = -1 := by
    calc
      (-ζ) * ζ = -(ζ * ζ) := by ring
      _ = -1 := by rw [hζ]
  simp only [zetaCommutator, smul_sub, smul_smul]
  rw [hneg, neg_one_smul]
  module

/-- The self bracket is `(1 - ζ) A²`. -/
theorem zetaCommutator_self {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ : ℂ) (a : A) :
    zetaCommutator ζ a a = (1 - ζ) • (a * a) := by
  simp [zetaCommutator, sub_smul]

/-- Mixed-sign product rule in the right argument. -/
theorem zetaCommutator_mul_right
    {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ η : ℂ) (a b c : A) :
    zetaCommutator (ζ * η) a (b * c) =
      zetaCommutator ζ a b * c + ζ • (b * zetaCommutator η a c) := by
  simp only [zetaCommutator, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul]
  simp only [mul_assoc]
  module

/-- Mixed-sign product rule in the left argument. -/
theorem zetaCommutator_mul_left
    {A : Type*} [Ring A] [Algebra ℂ A]
    (ζ η : ℂ) (a b c : A) :
    zetaCommutator (ζ * η) (a * b) c =
      a * zetaCommutator η b c + η • (zetaCommutator ζ a c * b) := by
  simp only [zetaCommutator, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul]
  simp only [mul_assoc]
  rw [mul_comm ζ η]
  module

/-- The exchange terms generated while pushing one labelled algebra element through a finite tail. -/
noncomputable def peelSum {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (element : Label → A) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) : List Label → A
  | [] => 0
  | D :: t =>
      exchangeCoeff C D • (t.map element).prod +
        ζ • (element D * peelSum element exchangeCoeff ζ C t)

@[simp]
theorem peelSum_nil {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (element : Label → A) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) :
    peelSum element exchangeCoeff ζ C [] = 0 := rfl

/-- Repeatedly apply a scalar exchange relation while pushing one algebra element through a finite
ordered product. -/
theorem mul_prod_eq_peelSum
    {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (element : Label → A) (exchangeCoeff : Label → Label → ℂ) (ζ : ℂ)
    (hExchange : ∀ C D,
      element C * element D =
        exchangeCoeff C D • (1 : A) + ζ • (element D * element C))
    (C : Label) (l : List Label) :
    element C * (l.map element).prod =
      peelSum element exchangeCoeff ζ C l +
        ζ ^ l.length • ((l.map element).prod * element C) := by
  induction l with
  | nil =>
      simp [peelSum]
  | cons D t ih =>
      simp only [List.map_cons, List.prod_cons, peelSum, List.length_cons]
      rw [← mul_assoc, hExchange C D, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
      rw [mul_assoc (element D) (element C) _, ih, mul_add, mul_smul_comm]
      rw [smul_add, smul_smul, pow_succ, ← mul_assoc]
      module

end ScalarExchange
