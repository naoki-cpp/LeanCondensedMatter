import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar resolvent algebra

Model-independent partial fractions for two shifts of the same scalar.
Unlike operator resolvent identities, this result works over any commutative
field. It neither assumes distinct spectral parameters nor divides by
their difference.
-/

namespace Algebra

/-- For two scalar resolvents of the same shift, multiplying their product by
the spectral-parameter difference gives the difference of resolvents. -/
theorem scalarResolvent_gap_mul_inverse_product
    {K : Type*} [Field K] (a b x : K)
    (ha : a - x ≠ 0) (hb : b - x ≠ 0) :
    (b - a) * ((a - x) * (b - x))⁻¹ =
      (a - x)⁻¹ - (b - x)⁻¹ := by
  have hgap : b - a = (b - x) - (a - x) := by ring
  rw [hgap]
  field_simp [ha, hb] <;> ring

end Algebra
