import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Finite-product counting

A sum whose summand depends only on the first coordinate of a finite product repeats each base value
once for every element of the second factor.  The statement is phrased through an equivalence so
that downstream code can use its own product decomposition directly.
-/

namespace Fintype

/-- Reindexing a finite type as `β × γ` counts a first-coordinate summand `card γ` times. -/
theorem sum_equiv_fst_eq_card_mul_sum {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (e : α ≃ β × γ) (f : β → ℕ) :
    (∑ x : α, f (e x).1) = card γ * ∑ y : β, f y := by
  rw [← Equiv.sum_comp e.symm, sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  calc
    (∑ y : β, ∑ _z : γ, f y) = ∑ y : β, card γ * f y := by
      apply Finset.sum_congr rfl
      intro y _
      simp
    _ = card γ * ∑ y : β, f y := by rw [Finset.mul_sum]

end Fintype
