module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

public section

set_option linter.style.header false

/-!
# Finite-type sums, products, and counting

Generic finite-product identities used by combinatorial decompositions. In particular, an arbitrary
finite type can be reindexed as a dependent sum and products can then be split fiberwise.
Antisymmetric double sums vanish when the diagonal vanishes, including in additive groups
with elements of order two.
-/

namespace Fintype

/-- Reindex a commutative product through an equivalence with a dependent sum and split it
into the product over the base and each fiber. -/
theorem prod_equiv_sigma {α ι M : Type*} [Fintype α] [Fintype ι]
    {F : ι → Type*} [∀ i, Fintype (F i)] [CommMonoid M]
    (e : α ≃ Σ i, F i) (f : α → M) :
    (∏ x : α, f x) = ∏ i : ι, ∏ y : F i, f (e.symm ⟨i, y⟩) := by
  simpa only [Fintype.prod_sigma] using (Equiv.prod_comp e.symm f).symm

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

namespace Combinatorics

/-- An antisymmetric function with zero diagonal has vanishing double sum. -/
theorem sum_antisymmetric_eq_zero {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (f : ι → ι → A) (hanti : ∀ x y, f x y = -f y x)
    (hdiag : ∀ x, f x x = 0) :
    (∑ x : ι, ∑ y : ι, f x y) = 0 := by
  classical
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · rintro ⟨x, y⟩
    change f x y + f y x = 0
    rw [hanti x y, neg_add_cancel]
  · rintro ⟨x, y⟩ hne hswap
    have h : y = x := congrArg Prod.fst hswap
    subst y
    exact hne (hdiag x)
  · rintro ⟨x, y⟩
    rfl

end Combinatorics
