import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite scalar-exchange peel

Repeatedly applies a supplied scalar exchange relation through an ordered finite product in an
associative unital complex algebra. The construction depends only on the exchange relation itself,
so both algebraic and bounded operator realizations can use the same peel theorem.
-/

namespace ScalarExchange

/-- The exchange terms generated while pushing one labelled algebra element through a finite tail. -/
noncomputable def peelSum {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (operator : Label → A) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) : List Label → A
  | [] => 0
  | D :: t =>
      exchangeCoeff C D • (t.map operator).prod +
        ζ • (operator D * peelSum operator exchangeCoeff ζ C t)

@[simp]
theorem peelSum_nil {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (operator : Label → A) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) :
    peelSum operator exchangeCoeff ζ C [] = 0 := rfl

/-- Repeatedly apply a scalar exchange relation while pushing one algebra element through a finite
ordered product. -/
theorem mul_prod_eq_peelSum
    {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (operator : Label → A) (exchangeCoeff : Label → Label → ℂ) (ζ : ℂ)
    (hExchange : ∀ C D,
      operator C * operator D =
        exchangeCoeff C D • (1 : A) + ζ • (operator D * operator C))
    (C : Label) (l : List Label) :
    operator C * (l.map operator).prod =
      peelSum operator exchangeCoeff ζ C l +
        ζ ^ l.length • ((l.map operator).prod * operator C) := by
  induction l with
  | nil =>
      simp [peelSum]
  | cons D t ih =>
      simp only [List.map_cons, List.prod_cons, peelSum, List.length_cons]
      rw [← mul_assoc, hExchange C D, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
      rw [mul_assoc (operator D) (operator C) _, ih, mul_add, mul_smul_comm]
      rw [smul_add, smul_smul, pow_succ, ← mul_assoc]
      module

end ScalarExchange
