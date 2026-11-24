module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Algebra.Basic

public section

set_option linter.style.header false

/-!
# Quadratic normalization and signed projectors in algebras over fields

An element whose square is a nonzero scalar square times the identity
becomes an involution when normalized by that scalar. Its signed half-sums are
idempotents and diagonalize scalar shifts of the original element.
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

section Projectors

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

/-- An involution acts on the signed projector numerator by its sign. -/
private theorem involution_mul_one_add (Q : A) (hQ : Q * Q = 1)
    (s : K) (hs : s ^ 2 = 1) :
    Q * ((1 : A) + s • Q) =
      s • ((1 : A) + s • Q) := by
  rw [mul_add, mul_one, mul_smul_comm, hQ]
  rw [smul_add, smul_smul]
  rw [show s * s = 1 by simpa [pow_two] using hs, one_smul]
  module

/-- The signed projector of a quadratic algebra element is an eigenprojector even
after adding a scalar shift. This requires only `H² = E² I`, `E ≠ 0`, and `s² = 1`. -/
theorem quadratic_shift_mul_projector
    (H : A) (E ε s : K) (hE : E ≠ 0)
    (hquad : H * H = E ^ 2 • (1 : A))
    (hs : s ^ 2 = 1) :
    (ε • (1 : A) + H) *
        ((1 / 2 : K) • ((1 : A) + (s / E) • H)) =
      (ε + s * E) •
        ((1 / 2 : K) • ((1 : A) + (s / E) • H)) := by
  let Q : A := E⁻¹ • H
  have hQ : Q * Q = 1 := inv_smul_mul_self_eq_one H E hE hquad
  have hH : H = E • Q := (smul_inv_smul₀ hE H).symm
  have hP :
      ((1 / 2 : K) • ((1 : A) + (s / E) • H)) =
        (1 / 2 : K) • ((1 : A) + s • Q) := by
    simp [Q, div_eq_mul_inv, smul_smul]
  rw [hP, hH]
  rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, mul_smul_comm,
    involution_mul_one_add Q hQ s hs]
  module

/-- The half-sum of the identity and a signed involution is idempotent. -/
private theorem involution_projector_mul_self (Q : A) (hQ : Q * Q = 1)
    (s : K) (hs : s ^ 2 = 1) :
    ((1 / 2 : K) • ((1 : A) + s • Q)) *
        ((1 / 2 : K) • ((1 : A) + s • Q)) =
      (1 / 2 : K) • ((1 : A) + s • Q) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [add_mul, one_mul, smul_mul_assoc,
    involution_mul_one_add Q hQ s hs, smul_smul]
  rw [show s * s = 1 by simpa [pow_two] using hs, one_smul]
  module

/-- The signed projector of an element with `H² = E² • 1` is idempotent. -/
theorem quadratic_projector_isIdempotent
    (H : A) (E s : K) (hE : E ≠ 0)
    (hquad : H * H = E ^ 2 • (1 : A))
    (hs : s ^ 2 = 1) :
    IsIdempotentElem ((1 / 2 : K) • ((1 : A) + (s / E) • H)) := by
  have hQ : (E⁻¹ • H) * (E⁻¹ • H) = 1 :=
    inv_smul_mul_self_eq_one H E hE hquad
  simpa [IsIdempotentElem, div_eq_mul_inv, smul_smul] using
    (involution_projector_mul_self (E⁻¹ • H) hQ s hs)

end Projectors

end Algebra
