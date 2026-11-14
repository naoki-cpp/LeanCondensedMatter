import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Scalar resolvent algebra: model-independent partial fractions over a field. -/

namespace Algebra

/-- A common scalar shift cancels from the two-resolvent difference.
No assumption that the spectral parameters are distinct is needed. -/
theorem scalarResolvent_gap_mul_inverse_product
    {K : Type*} [Field K] (a b x : K)
    (ha : a - x ≠ 0) (hb : b - x ≠ 0) :
    (b - a) * ((a - x) * (b - x))⁻¹ =
      (a - x)⁻¹ - (b - x)⁻¹ := by
  have hgap : b - a = (b - x) - (a - x) := by ring
  rw [hgap]
  field_simp [ha, hb]

/-- Imaginary part after multiplication by a squared inverse of a nonzero real gap. -/
theorem inv_real_gap_sq_mul_im (gap : ℝ) (z : ℂ) (hgap : gap ≠ 0) :
    (((gap : ℂ)⁻¹) ^ 2 * z).im = z.im / gap ^ 2 := by
  have hcoeff :
      (((gap : ℂ)⁻¹) ^ 2 = ((gap⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]
  rw [hcoeff]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  field_simp [hgap]
  ring

/-- Products of complex numerators with a shared real gap have the expected imaginary part. -/
theorem mul_div_real_gap_im (a b : ℂ) (gap : ℝ) (hgap : gap ≠ 0) :
    ((a / (gap : ℂ)) * (b / (gap : ℂ))).im =
      (a * b).im / gap ^ 2 := by
  rw [show (a / (gap : ℂ)) * (b / (gap : ℂ)) =
      ((gap : ℂ)⁻¹) ^ 2 * (a * b) by
    simp only [div_eq_mul_inv]
    ring]
  exact inv_real_gap_sq_mul_im gap (a * b) hgap

end Algebra
