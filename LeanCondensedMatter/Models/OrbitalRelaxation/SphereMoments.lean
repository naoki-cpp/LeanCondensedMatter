import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
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
  have h2 : IntervalIntegrable (fun u : ℝ => u ^ 2) volume
      (Real.cos Real.pi) (Real.cos (0 : ℝ)) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have h4 : IntervalIntegrable (fun u : ℝ => u ^ 4) volume
      (Real.cos Real.pi) (Real.cos (0 : ℝ)) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_sub h2 h4] at h
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
  simp only [sub_zero, mul_zero, Real.sin_zero]
  have hperiod : 4 * (2 * Real.pi) = (8 : ℕ) * Real.pi := by ring
  rw [hperiod, Real.sin_nat_mul_pi]
  ring

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
    have hA : IntervalIntegrable
        (fun φ : ℝ => (a * U) * Real.cos φ ^ 4) volume 0 (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
    have hB : IntervalIntegrable
        (fun φ : ℝ => (b * U) * Real.sin φ ^ 4) volume 0 (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
    have hC : IntervalIntegrable
        (fun _φ : ℝ => c * V) volume 0 (2 * Real.pi) :=
      continuous_const.intervalIntegrable _ _
    have hD : IntervalIntegrable
        (fun φ : ℝ => (d * U) * (Real.sin φ ^ 2 * Real.cos φ ^ 2))
        volume 0 (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
    have hE : IntervalIntegrable
        (fun φ : ℝ => (e * W) * Real.cos φ ^ 2) volume 0 (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
    have hF : IntervalIntegrable
        (fun φ : ℝ => (f * W) * Real.sin φ ^ 2) volume 0 (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
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
  unfold sphericalAverage
  simp_rw [hφ]
  have hA : IntervalIntegrable
      (fun θ : ℝ =>
        (r ^ 4 * Real.pi * (3 * (a + b) + d) / 4) * Real.sin θ ^ 5)
      volume 0 Real.pi := Continuous.intervalIntegrable (by fun_prop) _ _
  have hB : IntervalIntegrable
      (fun θ : ℝ =>
        (r ^ 4 * Real.pi * (2 * c)) * (Real.sin θ * Real.cos θ ^ 4))
      volume 0 Real.pi := Continuous.intervalIntegrable (by fun_prop) _ _
  have hC : IntervalIntegrable
      (fun θ : ℝ =>
        (r ^ 4 * Real.pi * (e + f)) *
          (Real.sin θ ^ 3 * Real.cos θ ^ 2))
      volume 0 Real.pi := Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_add (hA.add hB) hC,
    intervalIntegral.integral_add hA hB]
  simp only [intervalIntegral.integral_const_mul,
    integral_sin_five, integral_sin_mul_cos_four, integral_sin_three_mul_cos_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring


/-! ### Fourth moments deduced from the general quartic integral -/

/-- Continuous and finite fourth moments agree for every Cartesian index. -/
theorem sphericalAverage_coordinate_four (i : Fin 3) (r : ℝ) :
    sphericalAverage r (fun k => k i ^ 4) =
      evenQuarticCubature r (fun k => k i ^ 4) := by
  rw [evenQuarticCubature_coordinate_four]
  fin_cases i
  · have hf : evenQuarticPolynomial 1 0 0 0 0 0 =
        (fun k : Fin 3 → ℝ => k 0 ^ 4) := by
      funext k
      simp [evenQuarticPolynomial]
    change sphericalAverage r (fun k : Fin 3 → ℝ => k 0 ^ 4) = r ^ 4 / 5
    rw [← hf]
    simpa using (sphericalAverage_evenQuarticPolynomial r 1 0 0 0 0 0)
  · have hf : evenQuarticPolynomial 0 1 0 0 0 0 =
        (fun k : Fin 3 → ℝ => k 1 ^ 4) := by
      funext k
      simp [evenQuarticPolynomial]
    change sphericalAverage r (fun k : Fin 3 → ℝ => k 1 ^ 4) = r ^ 4 / 5
    rw [← hf]
    simpa using (sphericalAverage_evenQuarticPolynomial r 0 1 0 0 0 0)
  · have hf : evenQuarticPolynomial 0 0 1 0 0 0 =
        (fun k : Fin 3 → ℝ => k 2 ^ 4) := by
      funext k
      simp [evenQuarticPolynomial]
    change sphericalAverage r (fun k : Fin 3 → ℝ => k 2 ^ 4) = r ^ 4 / 5
    rw [← hf]
    simpa using (sphericalAverage_evenQuarticPolynomial r 0 0 1 0 0 0)

/-- Continuous and finite mixed fourth moments agree for distinct indices. -/
theorem sphericalAverage_coordinate_sq_mul_coordinate_sq (i j : Fin 3)
    (hij : i ≠ j) (r : ℝ) :
    sphericalAverage r (fun k => k i ^ 2 * k j ^ 2) =
      evenQuarticCubature r (fun k => k i ^ 2 * k j ^ 2) := by
  rw [evenQuarticCubature_coordinate_sq_mul_coordinate_sq i j hij]
  fin_cases i <;> fin_cases j <;>
    first
    | exact (hij rfl).elim
    | solve
      | convert sphericalAverage_evenQuarticPolynomial r 0 0 0 1 0 0 using 1 <;>
          (solve | ring | (congr 1; funext k; simp [evenQuarticPolynomial]; ring))
      | convert sphericalAverage_evenQuarticPolynomial r 0 0 0 0 1 0 using 1 <;>
          (solve | ring | (congr 1; funext k; simp [evenQuarticPolynomial]; ring))
      | convert sphericalAverage_evenQuarticPolynomial r 0 0 0 0 0 1 using 1 <;>
          (solve | ring | (congr 1; funext k; simp [evenQuarticPolynomial]; ring))

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
  · convert sphericalAverage_evenQuartic_eq_cubature r
      0 (c₁ ^ 2) (c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2)
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) using 1 <;>
      (congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring)
  · convert sphericalAverage_evenQuartic_eq_cubature r
      (c₁ ^ 2) 0 (c₁ ^ 2) (c₂ ^ 2)
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) using 1 <;>
      (congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring)
  · convert sphericalAverage_evenQuartic_eq_cubature r
      (c₁ ^ 2) (c₁ ^ 2) 0
      (4 * c₂ ^ 2 - 2 * c₁ ^ 2) (c₂ ^ 2) (c₂ ^ 2) using 1 <;>
      (congr 1; funext k; simp [orbitalPolynomial, evenQuarticPolynomial]; ring)

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


/-- The previously defined finite-model rate equals the continuous
spherical-coordinate average of its exact matrix double commutator.
This replaces the cubature numerically on this quartic integrand only;
the second-order kinetic closure remains a separate physical assumption. -/
theorem orbitalRate_eq_sphericalAverage (axis : Fin 3)
    (ℏ τ₂ c₁ c₂ r : ℝ) :
    orbitalRate axis ℏ τ₂ c₁ c₂ r =
      τ₂ / ℏ ^ 2 * sphericalAverage r
        (orbitalDoubleCommutator axis c₁ c₂) := by
  rw [orbitalRate, evenQuarticCubature_orbitalDoubleCommutator,
    sphericalAverage_orbitalDoubleCommutator]

end QuantumTheory.Models.OrbitalRelaxation
