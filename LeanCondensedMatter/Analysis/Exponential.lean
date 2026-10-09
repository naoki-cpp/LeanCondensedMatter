import Mathlib.Analysis.Complex.Trigonometric

set_option linter.style.header false

/-!
# Complex exponential away from one

A nonzero real part makes the modulus of the exponential different from one.
-/

namespace Complex

/-- A complex exponential cannot equal one when its exponent has nonzero real part. -/
theorem exp_ne_one_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) : exp z ≠ 1 := by
  intro h
  apply hz
  have hnorm := congrArg norm h
  rw [norm_exp, norm_one] at hnorm
  exact Real.exp_eq_one_iff.mp hnorm

end Complex
