import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Algebra.Basic

set_option linter.style.header false

/-!
# Quadratic normalization in algebras over fields

An element whose square is a nonzero scalar square times the identity
becomes an involution when normalized by that scalar.
-/

namespace Algebra

/-- If `H² = E² • 1` and `E ≠ 0`, then the normalized element
`E⁻¹ • H` is an involution. -/
theorem inv_smul_mul_self_eq_one
    {K A : Type*} [Field K] [Semiring A] [Algebra K A]
    (H : A) (E : K) (hE : E ≠ 0)
    (hquad : H * H = E ^ 2 • (1 : A)) :
    (E⁻¹ • H) * (E⁻¹ • H) = 1 := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hquad, smul_smul]
  have hcoeff : E⁻¹ * E⁻¹ * E ^ 2 = 1 := by
    field_simp [hE]
  rw [hcoeff, one_smul]

end Algebra
