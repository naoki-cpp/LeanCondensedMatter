import Mathlib.Algebra.Group.Basic

set_option linter.style.header false

/-!
# Affine fixed-point uniqueness

This module records the additive algebra behind linear ladder fixed-point equations. No finite
-dimensionality, topology, norm, or linear structure is required: uniqueness follows whenever the
shifted map `x ↦ x - f x` is injective.
-/

namespace Function

/-- If `x ↦ x - f x` is injective, the affine fixed-point equation `x = source + f x` has at most
one solution. -/
theorem eq_of_eq_add_apply_of_eq_add_apply_of_injective_sub_apply
    {α : Type*} [AddCommGroup α]
    (f : α → α)
    (hinjective : Function.Injective fun x => x - f x)
    {source left right : α}
    (hleft : left = source + f left)
    (hright : right = source + f right) :
    left = right := by
  apply hinjective
  have hleftShifted : left - f left = source := (sub_eq_iff_eq_add).2 hleft
  have hrightShifted : right - f right = source := (sub_eq_iff_eq_add).2 hright
  exact hleftShifted.trans hrightShifted.symm

end Function
