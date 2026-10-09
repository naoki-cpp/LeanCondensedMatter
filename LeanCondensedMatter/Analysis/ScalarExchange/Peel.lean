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

/-- The recursive exchange sum is a finite sum over the removed position. The remaining factors
retain their original order; no commutativity or exchange relation is required. -/
theorem peelSum_eq_sum {Label A : Type*} [Semiring A] [Algebra ℂ A]
    (element : Label → A) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) (l : List Label) :
    peelSum element exchangeCoeff ζ C l =
      ∑ j : Fin l.length,
        (ζ ^ (j : ℕ) * exchangeCoeff C (l[(j : ℕ)]'j.isLt)) •
          ((l.eraseIdx j).map element).prod := by
  induction l with
  | nil => simp [peelSum]
  | cons D t ih =>
      rw [peelSum]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero,
        List.eraseIdx_cons_zero]
      congr 1
      rw [ih, Finset.mul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ,
        List.map_cons, List.prod_cons, pow_succ, mul_smul_comm, smul_smul]
      congr 1
      ring

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

/-- The exchange contributions generated while pushing one fixed algebra element through a list
of factors paired with their scalar exchange coefficients. -/
noncomputable def peelSumWithCoefficients {A : Type*} [Semiring A] [Algebra ℂ A]
    (ζ : ℂ) : List (A × ℂ) → A
  | [] => 0
  | (B, c) :: t =>
      c • (t.map Prod.fst).prod + ζ • (B * peelSumWithCoefficients ζ t)

@[simp]
theorem peelSumWithCoefficients_nil {A : Type*} [Semiring A] [Algebra ℂ A]
    (ζ : ℂ) : peelSumWithCoefficients (A := A) ζ [] = 0 := rfl

/-- Position-indexed expansion when each factor carries its exchange coefficient. -/
theorem peelSumWithCoefficients_eq_sum {A : Type*} [Semiring A] [Algebra ℂ A]
    (ζ : ℂ) (l : List (A × ℂ)) :
    peelSumWithCoefficients ζ l =
      ∑ j : Fin l.length,
        (ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2) •
          ((l.eraseIdx j).map Prod.fst).prod := by
  have h : peelSumWithCoefficients ζ l =
      peelSum Prod.fst (fun _ p => p.2) ζ (0, 0) l := by
    induction l with
    | nil => rfl
    | cons p t ih =>
        obtain ⟨B, c⟩ := p
        simp only [peelSumWithCoefficients, peelSum, ih]
  rw [h, peelSum_eq_sum]

/-- Repeatedly apply a scalar exchange relation between one fixed element and the factors of a
coefficient-paired list. This form is useful when the exchange coefficients depend on the fixed
element, so no relations between the factors themselves are required. -/
theorem mul_prod_eq_peelSumWithCoefficients
    {A : Type*} [Semiring A] [Algebra ℂ A]
    (ζ : ℂ) (C : A) (l : List (A × ℂ))
    (hExchange : ∀ p ∈ l,
      C * p.1 = p.2 • (1 : A) + ζ • (p.1 * C)) :
    C * (l.map Prod.fst).prod =
      peelSumWithCoefficients ζ l + ζ ^ l.length • ((l.map Prod.fst).prod * C) := by
  induction l with
  | nil => simp [peelSumWithCoefficients]
  | cons p t ih =>
      obtain ⟨B, c⟩ := p
      have hhead := hExchange (B, c) (by simp)
      have htail : ∀ q ∈ t,
          C * q.1 = q.2 • (1 : A) + ζ • (q.1 * C) := by
        intro q hq
        exact hExchange q (List.mem_cons_of_mem _ hq)
      have iht := ih htail
      simp only [List.map_cons, List.prod_cons, List.length_cons, peelSumWithCoefficients]
      rw [← mul_assoc, hhead, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
      rw [mul_assoc B C _, iht, mul_add, mul_smul_comm]
      rw [smul_add, smul_smul, pow_succ, ← mul_assoc]
      module

end ScalarExchange
