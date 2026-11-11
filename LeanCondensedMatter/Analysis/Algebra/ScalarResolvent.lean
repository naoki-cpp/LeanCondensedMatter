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

end Algebra
