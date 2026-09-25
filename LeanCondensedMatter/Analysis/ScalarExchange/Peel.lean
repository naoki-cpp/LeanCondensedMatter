import LeanCondensedMatter.Analysis.ScalarExchange.Basic

set_option linter.style.header false

/-!
# Scalar exchange peeling

Finite-product algebra for repeatedly pushing one labelled algebra element through an ordered tail
under a fixed scalar exchange relation. The underlying bracket identities live in
`Analysis.ScalarExchange.Basic`.
-/

namespace ScalarExchange

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
