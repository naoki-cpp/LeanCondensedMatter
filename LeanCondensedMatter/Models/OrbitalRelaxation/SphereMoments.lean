import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Continuous fourth moments of a spherical momentum shell

We define the normalized sphere average using the usual polar chart
`(θ, φ) ↦ r (sin θ cos φ, sin θ sin φ, cos θ)` and the area-element weight
`sin θ dθ dφ / (4π)`. Exact integrals of fourth-order monomials are computed
from Mathlib's trigonometric integral identities.

This is a continuous spherical-coordinate average, independent of the
finite cubature. It does not assert a comparison with Hausdorff surface
measure on the sphere or a Fermi-surface distribution.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

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

private theorem integral_sin_one :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) = 2 := by
  simpa using (integral_sin_pow_odd (n := 0))

private theorem integral_sin_three :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 3) = 4 / 3 := by
  convert (integral_sin_pow_odd (n := 1)) using 1
  norm_num

private theorem integral_sin_five :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 5) = 16 / 15 := by
  convert (integral_sin_pow_odd (n := 2)) using 1
  norm_num

private theorem integral_sin_three_mul_cos_sq :
    (∫ θ in (0 : ℝ)..Real.pi,
       Real.sin θ ^ 3 * Real.cos θ ^ 2) = 4 / 15 := by
  have hid (θ : ℝ) :
      Real.sin θ ^ 3 * Real.cos θ ^ 2 =
        Real.sin θ ^ 3 - Real.sin θ ^ 5 := by
    have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hc]
    ring
  simp_rw [hid]
  have hsplit :
      (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 3 - Real.sin θ ^ 5) =
        (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 3) -
        (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 5) :=
    intervalIntegral.integral_sub
      (Real.continuous_sin.pow 3 |>.intervalIntegrable _ _)
      (Real.continuous_sin.pow 5 |>.intervalIntegrable _ _)
  rw [hsplit, integral_sin_three, integral_sin_five]
  ring

private theorem integral_sin_mul_cos_four :
    (∫ θ in (0 : ℝ)..Real.pi,
       Real.sin θ * Real.cos θ ^ 4) = 2 / 5 := by
  have hid (θ : ℝ) :
      Real.sin θ * Real.cos θ ^ 4 =
        Real.sin θ - 2 * Real.sin θ ^ 3 + Real.sin θ ^ 5 := by
    have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    calc
      _ = Real.sin θ * (Real.cos θ ^ 2) ^ 2 := by ring
      _ = Real.sin θ * (1 - Real.sin θ ^ 2) ^ 2 := by rw [hc]
      _ = _ := by ring
  simp_rw [hid]
  have h1 : IntervalIntegrable Real.sin volume 0 Real.pi :=
    Real.continuous_sin.intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun θ : ℝ => 2 * Real.sin θ ^ 3) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_sin.pow 3)).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ 5) volume 0 Real.pi :=
    (Real.continuous_sin.pow 5).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.sub h3) h5,
      intervalIntegral.integral_sub h1 h3,
      intervalIntegral.integral_const_mul,
      integral_sin_one, integral_sin_three, integral_sin_five]
  ring

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
  rw [integral_cos_pow (n := 2)]
  rw [integral_cos_sq_full]
  simp
  ring

private theorem integral_sin_four_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ ^ 4) = 3 * Real.pi / 4 := by
  rw [integral_sin_pow (n := 2)]
  rw [integral_sin_sq_full]
  simp
  ring

private theorem integral_sin_sq_mul_cos_sq_full :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
       Real.sin φ ^ 2 * Real.cos φ ^ 2) = Real.pi / 4 := by
  rw [integral_sin_sq_mul_cos_sq]
  simp
  have hperiod : 4 * (2 * Real.pi) = (8 : ℕ) * Real.pi := by ring
  rw [hperiod, Real.sin_nat_mul_pi]
  ring

private theorem sphericalAverage_x_four (r : ℝ) :
    sphericalAverage r (fun k => k 0 ^ 4) = r ^ 4 / 5 := by
  unfold sphericalAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
         (sphericalMomentum r θ φ) 0 ^ 4) =
      (r * Real.sin θ) ^ 4 * (3 * Real.pi / 4) := by
    have hcoord (φ : ℝ) :
        (sphericalMomentum r θ φ) 0 =
          r * Real.sin θ * Real.cos φ := by rfl
    simp_rw [hcoord]
    have hmul (φ : ℝ) :
        (r * Real.sin θ * Real.cos φ) ^ 4 =
          (r * Real.sin θ) ^ 4 * Real.cos φ ^ 4 := by ring
    simp_rw [hmul]
    rw [intervalIntegral.integral_const_mul, integral_cos_four_full]
  simp_rw [hφ]
  have hθ (θ : ℝ) :
      ((r * Real.sin θ) ^ 4 * (3 * Real.pi / 4)) * Real.sin θ =
        (r ^ 4 * (3 * Real.pi / 4)) * Real.sin θ ^ 5 := by ring
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul, integral_sin_five]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  all_goals ring

private theorem sphericalAverage_z_four (r : ℝ) :
    sphericalAverage r (fun k => k 2 ^ 4) = r ^ 4 / 5 := by
  unfold sphericalAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
         (sphericalMomentum r θ φ) 2 ^ 4) =
      2 * Real.pi * (r * Real.cos θ) ^ 4 := by
    have hcoord (φ : ℝ) :
        (sphericalMomentum r θ φ) 2 = r * Real.cos θ := by rfl
    simp_rw [hcoord]
    rw [intervalIntegral.integral_const]
    ring
  simp_rw [hφ]
  have hθ (θ : ℝ) :
      (2 * Real.pi * (r * Real.cos θ) ^ 4) * Real.sin θ =
        (2 * Real.pi * r ^ 4) * (Real.sin θ * Real.cos θ ^ 4) := by ring
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul, integral_sin_mul_cos_four]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  all_goals ring


private theorem sphericalAverage_y_four (r : ℝ) :
    sphericalAverage r (fun k => k 1 ^ 4) = r ^ 4 / 5 := by
  unfold sphericalAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
         (sphericalMomentum r θ φ) 1 ^ 4) =
      (r * Real.sin θ) ^ 4 * (3 * Real.pi / 4) := by
    have hcoord (φ : ℝ) :
        (sphericalMomentum r θ φ) 1 =
          r * Real.sin θ * Real.sin φ := by rfl
    simp_rw [hcoord]
    have hmul (φ : ℝ) :
        (r * Real.sin θ * Real.sin φ) ^ 4 =
          (r * Real.sin θ) ^ 4 * Real.sin φ ^ 4 := by ring
    simp_rw [hmul]
    rw [intervalIntegral.integral_const_mul, integral_sin_four_full]
  simp_rw [hφ]
  have hθ (θ : ℝ) :
      ((r * Real.sin θ) ^ 4 * (3 * Real.pi / 4)) * Real.sin θ =
        (r ^ 4 * (3 * Real.pi / 4)) * Real.sin θ ^ 5 := by ring
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul, integral_sin_five]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  all_goals ring

private theorem sphericalAverage_xy (r : ℝ) :
    sphericalAverage r (fun k => k 0 ^ 2 * k 1 ^ 2) = r ^ 4 / 15 := by
  unfold sphericalAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
         (sphericalMomentum r θ φ) 0 ^ 2 *
           (sphericalMomentum r θ φ) 1 ^ 2) =
      (r * Real.sin θ) ^ 4 * (Real.pi / 4) := by
    have hx (φ : ℝ) :
        (sphericalMomentum r θ φ) 0 =
          r * Real.sin θ * Real.cos φ := by rfl
    have hy (φ : ℝ) :
        (sphericalMomentum r θ φ) 1 =
          r * Real.sin θ * Real.sin φ := by rfl
    simp_rw [hx, hy]
    have hmul (φ : ℝ) :
        (r * Real.sin θ * Real.cos φ) ^ 2 *
          (r * Real.sin θ * Real.sin φ) ^ 2 =
          (r * Real.sin θ) ^ 4 *
            (Real.sin φ ^ 2 * Real.cos φ ^ 2) := by ring
    simp_rw [hmul]
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul_cos_sq_full]
  simp_rw [hφ]
  have hθ (θ : ℝ) :
      ((r * Real.sin θ) ^ 4 * (Real.pi / 4)) * Real.sin θ =
        (r ^ 4 * (Real.pi / 4)) * Real.sin θ ^ 5 := by ring
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul, integral_sin_five]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  all_goals ring

private theorem sphericalAverage_xz (r : ℝ) :
    sphericalAverage r (fun k => k 0 ^ 2 * k 2 ^ 2) = r ^ 4 / 15 := by
  unfold sphericalAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
         (sphericalMomentum r θ φ) 0 ^ 2 *
           (sphericalMomentum r θ φ) 2 ^ 2) =
      (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2) * Real.pi := by
    have hx (φ : ℝ) :
        (sphericalMomentum r θ φ) 0 =
          r * Real.sin θ * Real.cos φ := by rfl
    have hz (φ : ℝ) :
        (sphericalMomentum r θ φ) 2 = r * Real.cos θ := by rfl
    simp_rw [hx, hz]
    have hmul (φ : ℝ) :
        (r * Real.sin θ * Real.cos φ) ^ 2 *
          (r * Real.cos θ) ^ 2 =
          (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2) *
            Real.cos φ ^ 2 := by ring
    simp_rw [hmul]
    rw [intervalIntegral.integral_const_mul, integral_cos_sq_full]
  simp_rw [hφ]
  have hθ (θ : ℝ) :
      ((r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2) * Real.pi) *
        Real.sin θ =
        (r ^ 4 * Real.pi) *
          (Real.sin θ ^ 3 * Real.cos θ ^ 2) := by ring
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul, integral_sin_three_mul_cos_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

private theorem sphericalAverage_yz (r : ℝ) :
    sphericalAverage r (fun k => k 1 ^ 2 * k 2 ^ 2) = r ^ 4 / 15 := by
  unfold sphericalAverage
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
         (sphericalMomentum r θ φ) 1 ^ 2 *
           (sphericalMomentum r θ φ) 2 ^ 2) =
      (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2) * Real.pi := by
    have hy (φ : ℝ) :
        (sphericalMomentum r θ φ) 1 =
          r * Real.sin θ * Real.sin φ := by rfl
    have hz (φ : ℝ) :
        (sphericalMomentum r θ φ) 2 = r * Real.cos θ := by rfl
    simp_rw [hy, hz]
    have hmul (φ : ℝ) :
        (r * Real.sin θ * Real.sin φ) ^ 2 *
          (r * Real.cos θ) ^ 2 =
          (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2) *
            Real.sin φ ^ 2 := by ring
    simp_rw [hmul]
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_full]
  simp_rw [hφ]
  have hθ (θ : ℝ) :
      ((r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2) * Real.pi) *
        Real.sin θ =
        (r ^ 4 * Real.pi) *
          (Real.sin θ ^ 3 * Real.cos θ ^ 2) := by ring
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul, integral_sin_three_mul_cos_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The normalized continuous spherical-coordinate average of each fourth
Cartesian momentum moment equals the corresponding finite cubature value. -/
theorem sphericalAverage_coordinate_four (i : Fin 3) (r : ℝ) :
    sphericalAverage r (fun k => k i ^ 4) =
      evenQuarticCubature r (fun k => k i ^ 4) := by
  rw [evenQuarticCubature_coordinate_four]
  fin_cases i
  · exact sphericalAverage_x_four r
  · exact sphericalAverage_y_four r
  · exact sphericalAverage_z_four r

/-- The continuous spherical-coordinate mixed fourth moments coincide with
the finite cubature for two distinct Cartesian indices. -/
theorem sphericalAverage_coordinate_sq_mul_coordinate_sq (i j : Fin 3)
    (hij : i ≠ j) (r : ℝ) :
    sphericalAverage r (fun k => k i ^ 2 * k j ^ 2) =
      evenQuarticCubature r (fun k => k i ^ 2 * k j ^ 2) := by
  rw [evenQuarticCubature_coordinate_sq_mul_coordinate_sq i j hij]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact sphericalAverage_xy r
  · exact sphericalAverage_xz r
  · have hs : (fun k : Fin 3 → ℝ => k 1 ^ 2 * k 0 ^ 2) =
        (fun k => k 0 ^ 2 * k 1 ^ 2) := by
      funext k
      ring
    change sphericalAverage r (fun k : Fin 3 → ℝ => k 1 ^ 2 * k 0 ^ 2) =
      r ^ 4 / 15
    rw [hs]
    exact sphericalAverage_xy r
  · exact (hij rfl).elim
  · exact sphericalAverage_yz r
  · have hs : (fun k : Fin 3 → ℝ => k 2 ^ 2 * k 0 ^ 2) =
        (fun k => k 0 ^ 2 * k 2 ^ 2) := by
      funext k
      ring
    change sphericalAverage r (fun k : Fin 3 → ℝ => k 2 ^ 2 * k 0 ^ 2) =
      r ^ 4 / 15
    rw [hs]
    exact sphericalAverage_xz r
  · have hs : (fun k : Fin 3 → ℝ => k 2 ^ 2 * k 1 ^ 2) =
        (fun k => k 1 ^ 2 * k 2 ^ 2) := by
      funext k
      ring
    change sphericalAverage r (fun k : Fin 3 → ℝ => k 2 ^ 2 * k 1 ^ 2) =
      r ^ 4 / 15
    rw [hs]
    exact sphericalAverage_yz r
  · exact (hij rfl).elim


/-- The six coordinate-even homogeneous quartic monomials in three variables. -/
private def evenQuarticPolynomial (a b c d e f : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  a * k 0 ^ 4 + b * k 1 ^ 4 + c * k 2 ^ 4 +
    d * (k 0 ^ 2 * k 1 ^ 2) +
    e * (k 0 ^ 2 * k 2 ^ 2) +
    f * (k 1 ^ 2 * k 2 ^ 2)

/-- The normalized continuous spherical-coordinate average of any coordinate-even
homogeneous quartic, evaluated independently of the finite cubature. -/
private theorem sphericalAverage_evenQuarticPolynomial (r a b c d e f : ℝ) :
    sphericalAverage r (evenQuarticPolynomial a b c d e f) =
      r ^ 4 / 5 * (a + b + c) + r ^ 4 / 15 * (d + e + f) := by
  have hφ (θ : ℝ) :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
        evenQuarticPolynomial a b c d e f (sphericalMomentum r θ φ)) =
        (a * (r ^ 4 * Real.sin θ ^ 4)) * (3 * Real.pi / 4) +
        (b * (r ^ 4 * Real.sin θ ^ 4)) * (3 * Real.pi / 4) +
        (c * (r ^ 4 * Real.cos θ ^ 4)) * (2 * Real.pi) +
        (d * (r ^ 4 * Real.sin θ ^ 4)) * (Real.pi / 4) +
        (e * (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2)) * Real.pi +
        (f * (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2)) * Real.pi := by
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
    have hA : IntervalIntegrable
        (fun φ : ℝ => (a * U) * Real.cos φ ^ 4) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hB : IntervalIntegrable
        (fun φ : ℝ => (b * U) * Real.sin φ ^ 4) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hC : IntervalIntegrable
        (fun _φ : ℝ => c * V) volume 0 (2 * Real.pi) :=
      continuous_const.intervalIntegrable _ _
    have hD : IntervalIntegrable
        (fun φ : ℝ => (d * U) * (Real.sin φ ^ 2 * Real.cos φ ^ 2))
        volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hE : IntervalIntegrable
        (fun φ : ℝ => (e * W) * Real.cos φ ^ 2) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hF : IntervalIntegrable
        (fun φ : ℝ => (f * W) * Real.sin φ ^ 2) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [
      intervalIntegral.integral_add ((((hA.add hB).add hC).add hD).add hE) hF,
      intervalIntegral.integral_add (((hA.add hB).add hC).add hD) hE,
      intervalIntegral.integral_add ((hA.add hB).add hC) hD,
      intervalIntegral.integral_add (hA.add hB) hC,
      intervalIntegral.integral_add hA hB]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_cos_four_full, integral_sin_four_full,
      integral_sin_sq_mul_cos_sq_full, integral_cos_sq_full, integral_sin_sq_full]
    dsimp [U, V, W]
    ring
  have hθ (θ : ℝ) :
      ((a * (r ^ 4 * Real.sin θ ^ 4)) * (3 * Real.pi / 4) +
        (b * (r ^ 4 * Real.sin θ ^ 4)) * (3 * Real.pi / 4) +
        (c * (r ^ 4 * Real.cos θ ^ 4)) * (2 * Real.pi) +
        (d * (r ^ 4 * Real.sin θ ^ 4)) * (Real.pi / 4) +
        (e * (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2)) * Real.pi +
        (f * (r ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2)) * Real.pi) *
          Real.sin θ =
        (r ^ 4 * Real.pi * (3 * (a + b) + d) / 4) * Real.sin θ ^ 5 +
        (r ^ 4 * Real.pi * (2 * c)) * (Real.sin θ * Real.cos θ ^ 4) +
        (r ^ 4 * Real.pi * (e + f)) *
          (Real.sin θ ^ 3 * Real.cos θ ^ 2) := by
    ring
  unfold sphericalAverage
  simp_rw [hφ, hθ]
  have hA : IntervalIntegrable
      (fun θ : ℝ =>
        (r ^ 4 * Real.pi * (3 * (a + b) + d) / 4) * Real.sin θ ^ 5)
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hB : IntervalIntegrable
      (fun θ : ℝ =>
        (r ^ 4 * Real.pi * (2 * c)) * (Real.sin θ * Real.cos θ ^ 4))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hC : IntervalIntegrable
      (fun θ : ℝ =>
        (r ^ 4 * Real.pi * (e + f)) *
          (Real.sin θ ^ 3 * Real.cos θ ^ 2))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add (hA.add hB) hC,
    intervalIntegral.integral_add hA hB]
  simp only [intervalIntegral.integral_const_mul,
    integral_sin_five, integral_sin_mul_cos_four, integral_sin_three_mul_cos_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- Exactness of the finite cubature on *all* coordinate-even homogeneous
quartics, justified by the continuous spherical-coordinate integral. -/
private theorem sphericalAverage_evenQuartic_eq_cubature (r a b c d e f : ℝ) :
    sphericalAverage r (evenQuarticPolynomial a b c d e f) =
      evenQuarticCubature r (evenQuarticPolynomial a b c d e f) := by
  rw [sphericalAverage_evenQuarticPolynomial]
  simp [evenQuarticCubature, evenQuarticPolynomial]
  ring

/-- The orbital double-commutator quartic has the same continuous spherical
average as the finite cubature, for all three Cartesian polarizations. -/
theorem sphericalAverage_orbitalPolynomial_eq_cubature (axis : Fin 3)
    (c₁ c₂ r : ℝ) :
    sphericalAverage r (orbitalPolynomial axis c₁ c₂) =
      evenQuarticCubature r (orbitalPolynomial axis c₁ c₂) := by
  fin_cases axis
  · have h : orbitalPolynomial (0 : Fin 3) c₁ c₂ =
        evenQuarticPolynomial 0 (c₁ ^ 2) (c₁ ^ 2)
          (c₂ ^ 2) (c₂ ^ 2) (4 * c₂ ^ 2 - 2 * c₁ ^ 2) := by
      funext k
      simp [orbitalPolynomial, evenQuarticPolynomial]
      ring
    rw [h]
    exact sphericalAverage_evenQuartic_eq_cubature r
      0 (c₁ ^ 2) (c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2)
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2)
  · have h : orbitalPolynomial (1 : Fin 3) c₁ c₂ =
        evenQuarticPolynomial (c₁ ^ 2) 0 (c₁ ^ 2)
          (c₂ ^ 2) (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) := by
      funext k
      simp [orbitalPolynomial, evenQuarticPolynomial]
      ring
    rw [h]
    exact sphericalAverage_evenQuartic_eq_cubature r
      (c₁ ^ 2) 0 (c₁ ^ 2) (c₂ ^ 2)
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2)
  · have h : orbitalPolynomial (2 : Fin 3) c₁ c₂ =
        evenQuarticPolynomial (c₁ ^ 2) (c₁ ^ 2) 0
          (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2) := by
      funext k
      simp [orbitalPolynomial, evenQuarticPolynomial]
      ring
    rw [h]
    exact sphericalAverage_evenQuartic_eq_cubature r
      (c₁ ^ 2) (c₁ ^ 2) 0
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2)

/-- The exact matrix double commutator has the physical spherical-coordinate
fourth moment, without replacing the continuous angular integral by a cubature
assumption. -/
theorem sphericalAverage_orbitalDoubleCommutator (axis : Fin 3)
    (c₁ c₂ r : ℝ) :
    sphericalAverage r (orbitalDoubleCommutator axis c₁ c₂) =
      (2 * r ^ 4 / 15) * (2 * c₁ ^ 2 + 3 * c₂ ^ 2) := by
  have h : orbitalDoubleCommutator axis c₁ c₂ =
      orbitalPolynomial axis c₁ c₂ := by
    funext k
    exact orbitalDoubleCommutator_eq_polynomial axis c₁ c₂ k
  rw [h, sphericalAverage_orbitalPolynomial_eq_cubature,
    evenQuarticCubature_orbitalPolynomial]

end QuantumTheory.Models.OrbitalRelaxation
