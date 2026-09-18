import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Finite-product reindexing and counting

Generic finite-product identities used by combinatorial decompositions. In particular, an arbitrary
finite type can be reindexed as a dependent sum and products can then be split fiberwise.
-/

namespace Fintype

/-- Reindex a commutative product through an equivalence with a dependent sum and split it
into the product over the base and each fiber. -/
theorem prod_equiv_sigma {α ι M : Type*} [Fintype α] [Fintype ι]
    {F : ι → Type*} [∀ i, Fintype (F i)] [CommMonoid M]
    (e : α ≃ Σ i, F i) (f : α → M) :
    (∏ x : α, f x) = ∏ i : ι, ∏ y : F i, f (e.symm ⟨i, y⟩) := by
  calc
    (∏ x : α, f x) = ∏ z : Σ i, F i, f (e.symm z) :=
      (Equiv.prod_comp e.symm f).symm
    _ = ∏ i : ι, ∏ y : F i, f (e.symm ⟨i, y⟩) :=
      Fintype.prod_sigma _

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
