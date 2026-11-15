import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Scalar resolvent algebra: model-independent partial fractions over a field. -/

namespace Algebra

/-- The imaginary part of an inverse real-gap square, valid also at zero
because the inverse is totalized. -/
theorem inv_real_gap_sq_mul_im (gap : ℝ) (z : ℂ) :
    (((gap : ℂ)⁻¹) ^ 2 * z).im = (gap⁻¹ ^ 2) * z.im := by
  have hcoeff : (((gap : ℂ)⁻¹) ^ 2) = ((gap⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]
  rw [hcoeff]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- Products of complex numerators with a shared nonzero real gap have the expected imaginary part. -/
theorem mul_div_real_gap_im (a b : ℂ) (gap : ℝ) (hgap : gap ≠ 0) :
    ((a / (gap : ℂ)) * (b / (gap : ℂ))).im =
      (a * b).im / gap ^ 2 := by
  rw [show (a / (gap : ℂ)) * (b / (gap : ℂ)) =
      ((gap : ℂ)⁻¹) ^ 2 * (a * b) by
    simp only [div_eq_mul_inv]
    ring, inv_real_gap_sq_mul_im]
  field_simp [hgap]

end Algebra
