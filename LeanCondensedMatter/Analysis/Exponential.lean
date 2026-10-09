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
  have hnorm := congrArg norm (h.trans exp_zero.symm)
  simp only [norm_exp] at hnorm
  exact Real.exp_injective hnorm

end Complex
