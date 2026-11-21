import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Continuous fourth moments of a spherical momentum shell

We define the normalized sphere average using the usual polar chart
`(θ, φ) ↦ r (sin θ cos φ, sin θ sin φ, cos θ)` and the area-element weight
`sin θ dθ dφ / (4π)`. Exact integrals of fourth-order monomials are computed
from Mathlib's trigonometric integral identities.

This is a continuous spherical-coordinate average of generic real-valued functions,
independent of any physical model or finite cubature. It does not assert a
comparison with Hausdorff surface measure on the sphere.
-/

namespace SphericalMoments

open MeasureTheory
open scoped Interval

/-- Spherical coordinates at fixed (possibly signed) radial parameter. -/
noncomputable def sphericalMomentum (r θ φ : ℝ) : Fin 3 → ℝ :=
  ![r * Real.sin θ * Real.cos φ,
    r * Real.sin θ * Real.sin φ,
    r * Real.cos θ]

/-- Normalized continuous angular average in spherical coordinates. -/
noncomputable def sphericalAverage (r : ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..Real.pi,
    (∫ φ in (0 : ℝ)..(2 * Real.pi), f (sphericalMomentum r θ φ)) *
      Real.sin θ) / (4 * Real.pi)

private theorem integral_sin_five :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 5) = 16 / 15 := by
  convert (integral_sin_pow_odd (n := 2)) using 1
  norm_num

private theorem integral_sin_three_mul_cos_sq :
    (∫ θ in (0 : ℝ)..Real.pi,
       Real.sin θ ^ 3 * Real.cos θ ^ 2) = 4 / 15 := by
  have h := integral_sin_pow_odd_mul_cos_pow (a := (0 : ℝ)) (b := Real.pi) 1 2
  simp only [pow_one] at h
  have hid (u : ℝ) : u ^ 2 * (1 - u ^ 2) = u ^ 2 - u ^ 4 := by ring
  simp_rw [hid] at h
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)] at h
  norm_num [integral_pow] at h
  exact h

private theorem integral_sin_mul_cos_four :
    (∫ θ in (0 : ℝ)..Real.pi,
       Real.sin θ * Real.cos θ ^ 4) = 2 / 5 := by
  have h := integral_sin_pow_odd_mul_cos_pow (a := (0 : ℝ)) (b := Real.pi) 0 4
  norm_num [integral_pow] at h
  exact h

private theorem integral_cos_sq_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp

private theorem integral_sin_sq_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ ^ 2) = Real.pi := by
  rw [integral_sin_sq]
  simp

private theorem integral_cos_four_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ ^ 4) = 3 * Real.pi / 4 := by
  rw [integral_cos_pow (n := 2), integral_cos_sq_full]
  simp
  ring

private theorem integral_sin_four_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ ^ 4) = 3 * Real.pi / 4 := by
  rw [integral_sin_pow (n := 2), integral_sin_sq_full]
  simp
  ring

private theorem integral_sin_sq_mul_cos_sq_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
       Real.sin φ ^ 2 * Real.cos φ ^ 2) = Real.pi / 4 := by
  rw [integral_sin_sq_mul_cos_sq]
  simp only [sub_zero, mul_zero, Real.sin_zero]
  have hperiod : 4 * (2 * Real.pi) = (8 : ℕ) * Real.pi := by ring
  rw [hperiod, Real.sin_nat_mul_pi]
  ring

/-- The six coordinate-even homogeneous quartic monomials in three variables. -/
def evenQuarticPolynomial (a b c d e f : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  a * k 0 ^ 4 + b * k 1 ^ 4 + c * k 2 ^ 4 +
    d * (k 0 ^ 2 * k 1 ^ 2) +
    e * (k 0 ^ 2 * k 2 ^ 2) +
    f * (k 1 ^ 2 * k 2 ^ 2)

/-- The normalized continuous spherical-coordinate average of any coordinate-even
homogeneous quartic, evaluated independently of the finite cubature. -/
theorem sphericalAverage_evenQuarticPolynomial (r a b c d e f : ℝ) :
    sphericalAverage r (evenQuarticPolynomial a b c d e f) =
      r ^ 4 / 5 * (a + b + c) + r ^ 4 / 15 * (d + e + f) := by
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
        evenQuarticPolynomial a b c d e f (sphericalMomentum r θ φ)) *
          Real.sin θ =
        (r ^ 4 * Real.pi * (3 * (a + b) + d) / 4) * Real.sin θ ^ 5 +
        (r ^ 4 * Real.pi * (2 * c)) * (Real.sin θ * Real.cos θ ^ 4) +
        (r ^ 4 * Real.pi * (e + f)) *
          (Real.sin θ ^ 3 * Real.cos θ ^ 2) := by
    let U : ℝ := r ^ 4 * Real.sin θ ^ 4
    let V : ℝ := r ^ 4 * Real.cos θ ^ 4
    let W : ℝ := r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2
    have hpoint (φ : ℝ) :
        evenQuarticPolynomial a b c d e f (sphericalMomentum r θ φ) =
          (a * U) * Real.cos φ ^ 4 +
          (b * U) * Real.sin φ ^ 4 +
          c * V +
          (d * U) * (Real.sin φ ^ 2 * Real.cos φ ^ 2) +
          (e * W) * Real.cos φ ^ 2 +
          (f * W) * Real.sin φ ^ 2 := by
      simp [evenQuarticPolynomial, sphericalMomentum, U, V, W]
      ring
    simp_rw [hpoint]
    repeat' rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_cos_four_full, integral_sin_four_full,
      integral_sin_sq_mul_cos_sq_full, integral_cos_sq_full, integral_sin_sq_full]
    dsimp [U, V, W]
    ring
  unfold sphericalAverage
  simp_rw [hφ]
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [intervalIntegral.integral_const_mul,
    integral_sin_five, integral_sin_mul_cos_four, integral_sin_three_mul_cos_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring



/-! ### Cartesian fourth moments -/

/-- The normalized spherical fourth moment of any Cartesian coordinate is `r⁴/5`. -/
theorem sphericalAverage_coordinate_four (i : Fin 3) (r : ℝ) :
    sphericalAverage r (fun k => k i ^ 4) = r ^ 4 / 5 := by
  fin_cases i
  · simpa [evenQuarticPolynomial] using
      (sphericalAverage_evenQuarticPolynomial r 1 0 0 0 0 0)
  · simpa [evenQuarticPolynomial] using
      (sphericalAverage_evenQuarticPolynomial r 0 1 0 0 0 0)
  · simpa [evenQuarticPolynomial] using
      (sphericalAverage_evenQuarticPolynomial r 0 0 1 0 0 0)

/-- The normalized mixed spherical fourth moment for distinct coordinates is `r⁴/15`. -/
theorem sphericalAverage_coordinate_sq_mul_coordinate_sq (i j : Fin 3)
    (hij : i ≠ j) (r : ℝ) :
    sphericalAverage r (fun k => k i ^ 2 * k j ^ 2) = r ^ 4 / 15 := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact (hij rfl).elim
    | simpa [evenQuarticPolynomial, mul_comm] using
        (sphericalAverage_evenQuarticPolynomial r 0 0 0 1 0 0)
    | simpa [evenQuarticPolynomial, mul_comm] using
        (sphericalAverage_evenQuarticPolynomial r 0 0 0 0 1 0)
    | simpa [evenQuarticPolynomial, mul_comm] using
        (sphericalAverage_evenQuarticPolynomial r 0 0 0 0 0 1)


end SphericalMoments
