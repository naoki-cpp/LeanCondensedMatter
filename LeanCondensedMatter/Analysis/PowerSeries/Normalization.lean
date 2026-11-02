import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Basic.Complex.Basic

set_option linter.style.header false

/-!
# Normalization and logarithmic derivative of formal power series

For a power series with nonzero constant coefficient, multiplication by its inverse produces a
series with constant coefficient `1`. Mathlib's `PowerSeries.logOf` is the authoritative formal
logarithm. For a normalized series, the formal logarithmic derivative satisfies the usual product
identity.
-/

namespace PowerSeries

section ConstantCoeff

variable {R : Type*} [Field R]

/-- Normalize a power series by multiplying it by the inverse of its constant coefficient. -/
noncomputable def normalizeByConstantCoeff (Z : PowerSeries R) : PowerSeries R :=
  C (constantCoeff Z)⁻¹ * Z

/-- Coefficients of a normalized series are scaled by the inverse constant coefficient. -/
@[simp]
theorem coeff_normalizeByConstantCoeff (Z : PowerSeries R) (n : ℕ) :
    coeff n (normalizeByConstantCoeff Z) = (constantCoeff Z)⁻¹ * coeff n Z := by
  simp [normalizeByConstantCoeff]

/-- A power series normalized by a nonzero constant coefficient has constant coefficient `1`. -/
theorem constantCoeff_normalizeByConstantCoeff {Z : PowerSeries R}
    (hZ : constantCoeff Z ≠ 0) :
    constantCoeff (normalizeByConstantCoeff Z) = 1 := by
  rw [normalizeByConstantCoeff, map_mul, constantCoeff_C, inv_mul_cancel₀ hZ]

/-- Cancel a right power-series factor with invertible constant coefficient.

This is the formal algebra used after a coefficientwise factorization `source = normalized * vacuum`:
multiplying the source by the inverse vacuum series recovers the normalized factor. -/
theorem mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
    {source normalized vacuum : PowerSeries R}
    (hvacuum : constantCoeff vacuum ≠ 0)
    (hsource : source = normalized * vacuum) :
    source * vacuum⁻¹ = normalized := by
  rw [hsource, mul_assoc, PowerSeries.mul_inv_cancel vacuum hvacuum, mul_one]

/-- The order-one coefficient of `logOf Z` equals the order-one coefficient of a normalized
complex power series `Z`. -/
theorem coeff_one_logOf {Z : PowerSeries ℂ} (hZ : constantCoeff Z = 1) :
    coeff 1 (logOf Z) = coeff 1 Z := by
  have hsub : HasSubst (Z - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hZ1 : constantCoeff (Z - 1) = 0 := by simp [hZ]
  have hpow : ∀ d, 2 ≤ d → coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    have hd' : d - 1 ≠ 0 := by omega
    simp [coeff_one_pow, hZ1, hd']
  have hterm : ∀ d : ℕ, d ≠ 1 →
      coeff d (log ℂ) • coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · simp
    · simp [hpow d (by omega)]
  rw [logOf_eq, coeff_subst' hsub, finsum_eq_single _ 1 hterm, coeff_one_log,
    one_smul, pow_one, map_sub, coeff_one]
  simp

end ConstantCoeff

section LogDerivative

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Logarithmic derivative identity for a normalized power series over a rational algebra. -/
theorem derivative_logOf_mul {Z : PowerSeries R}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX (PowerSeries.logOf Z) * Z = d⁄dX Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries R => f.subst (Z - 1))
    derivative_log_mul_one_add_X
  have hone : (1 : PowerSeries R).subst (Z - 1) = 1 := by
    rw [show (1 : PowerSeries R) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hgeom' :
      (d⁄dX (PowerSeries.log R)).subst (Z - 1) * Z = 1 := by
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub, hone] at hgeom
    simpa using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsub]
  have hderiv : d⁄dX (Z - 1) = d⁄dX Z := by simp
  rw [hderiv]
  calc
    ((d⁄dX (PowerSeries.log R)).subst (Z - 1) * d⁄dX Z) * Z =
        ((d⁄dX (PowerSeries.log R)).subst (Z - 1) * Z) * d⁄dX Z := by
          ring
    _ = d⁄dX Z := by rw [hgeom']; simp

end LogDerivative

end PowerSeries
