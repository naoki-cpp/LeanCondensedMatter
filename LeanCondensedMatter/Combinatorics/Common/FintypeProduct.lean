module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

public section

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

/-- A first-coordinate sum is divisible by every divisor of the repeated fiber's cardinality. -/
theorem dvd_sum_equiv_fst_of_dvd_card {α β γ : Type*}
    [Fintype α] [Finite β] [Fintype γ]
    (e : α ≃ β × γ) (f : β → ℕ) {d : ℕ} (hcard : d ∣ card γ) :
    d ∣ ∑ x : α, f (e x).1 := by
  letI : Fintype β := Fintype.ofFinite β
  have hsum : (∑ x : α, f (e x).1) = card γ * ∑ y : β, f y := by
    rw [← Equiv.sum_comp e.symm, sum_prod_type]
    simp [Finset.mul_sum]
  rw [hsum]
  exact dvd_mul_of_dvd_left hcard _

end Fintype
