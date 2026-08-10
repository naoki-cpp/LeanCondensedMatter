import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Ordered-simplex integrals only see strictly decreasing time assignments

`orderedSimplexIntegral` is an iterated interval integral, each level ranging over `(0, τ i)`. Its
integrand is therefore only ever evaluated at strictly decreasing assignments, apart from one
endpoint per level, which a one-dimensional interval integral does not see.

So two integrands agreeing on strictly decreasing assignments have equal ordered-simplex integrals.
No measure theory on `Fin n → ℝ` is involved: the coincidence locus is not a positive-codimension
subset to be shown null, it is a single point of each nested interval.

This is what lets the two-point linked-cluster development use relabel covariance, which holds only
at injective interaction-time assignments — and a strictly decreasing assignment is injective.
-/

namespace Analysis

open MeasureTheory

/-- Prepending a value above a strictly decreasing family keeps it strictly decreasing. -/
private theorem strictAnti_cons {m : ℕ} {τ₀ : ℝ} {rest : Fin m → ℝ}
    (hrest : StrictAnti rest) (hb : ∀ i, rest i < τ₀) : StrictAnti (Fin.cons τ₀ rest) := by
  intro a b hab
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
  · exact absurd hab (lt_irrefl _)
  · simpa using hb j
  · exact absurd hab (Fin.not_lt_zero _)
  · simp only [Fin.cons_succ]
    exact hrest (Fin.succ_lt_succ_iff.mp hab)

/-- **Only strictly decreasing assignments matter.** Two integrands that agree on every strictly
decreasing assignment bounded by `β` have the same ordered-simplex integral. -/
theorem orderedSimplexIntegral_congr_of_strictAnti :
    ∀ (n : ℕ) (β : ℝ), 0 ≤ β → ∀ f g : (Fin n → ℝ) → ℂ,
      (∀ τ : Fin n → ℝ, StrictAnti τ → (∀ i, τ i < β) → f τ = g τ) →
        orderedSimplexIntegral n β f = orderedSimplexIntegral n β g := by
  intro n
  induction n with
  | zero =>
      intro β _ f g h
      exact h Fin.elim0 (fun a _ _ => a.elim0) (fun i => i.elim0)
  | succ m ih =>
      intro β hβ f g h
      rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
      have hne : ∀ᵐ τ₀ : ℝ, τ₀ ≠ β := by
        rw [MeasureTheory.ae_iff]
        simp
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne] with τ₀ hτ₀ hmem
      have hmem' : 0 < τ₀ ∧ τ₀ ≤ β := by
        rw [Set.uIoc_of_le hβ] at hmem
        exact ⟨hmem.1, hmem.2⟩
      have hlt : τ₀ < β := lt_of_le_of_ne hmem'.2 hτ₀
      refine ih τ₀ (le_of_lt hmem'.1) _ _ fun rest hanti hbound => ?_
      refine h (Fin.cons τ₀ rest) (strictAnti_cons hanti hbound) fun i => ?_
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simpa using hlt
      · simpa using lt_trans (hbound j) hlt

/-- The form the relabel covariance layer consumes: a strictly decreasing assignment is injective,
so an identity available only at injective interaction times still determines the integral. -/
theorem orderedSimplexIntegral_congr_of_injective (n : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (f g : (Fin n → ℝ) → ℂ)
    (h : ∀ τ : Fin n → ℝ, Function.Injective τ → f τ = g τ) :
    orderedSimplexIntegral n β f = orderedSimplexIntegral n β g :=
  orderedSimplexIntegral_congr_of_strictAnti n β hβ f g
    fun τ hanti _ => h τ hanti.injective

end Analysis
