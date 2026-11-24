import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Finite antisymmetric sums

Swapping the two indices pairs off all off-diagonal contributions.
The diagonal must vanish separately; antisymmetry alone does not imply this
in an additive group with nonzero elements of order two.
-/

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
