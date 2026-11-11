import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ

set_option linter.style.header false

/-!
# Velocity scaling of the fixed-center UV Fourier resolvent

The radial Fourier resolvent at general nonzero velocity reduces to
the corresponding integral at unit velocity and spectral center
`center / v²`. This file proves the exact finite-cutoff scaling and
transports it to the already constructed ultraviolet limits.

Unlike a bare change of notation, this factors the velocity out of the
**original regulated Fourier integral** prior to the UV limit. The
remaining upper-half-plane transform is a unit-velocity resolvent
problem; no contour integral or special-function identity is assumed
here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- Removing the velocity scale from the *finite-cutoff* resolvent
radial Fourier integral is an exact algebraic identity. -/
theorem massiveDiracRadialBesselJ_integral_scale_velocity
    (v c b : ℝ) (center : ℂ) (hv : v ≠ 0) :
    (∫ p in (0 : ℝ)..b,
      (p : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) *
          Complex.besselJ 0 ((p * c : ℝ) : ℂ)) *
        (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
      ((v : ℂ) ^ 2)⁻¹ *
        (∫ p in (0 : ℝ)..b,
          (p : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) *
              Complex.besselJ 0 ((p * c : ℝ) : ℂ)) *
            (center / (v : ℂ) ^ 2 - ((p ^ 2 : ℝ) : ℂ))⁻¹) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have hden :
      center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) =
        (v : ℂ) ^ 2 * (center / (v : ℂ) ^ 2 - ((p ^ 2 : ℝ) : ℂ)) := by
    push_cast
    field_simp [hvC]
  dsimp only
  rw [hden, mul_inv_rev]
  ring

/-- Nonreal spectral centers stay nonreal when divided by a
nonzero real squared velocity; the sign of their imaginary part is
also preserved. -/
theorem massiveDiracRadial_center_div_velocity_sq_im
    (v : ℝ) (center : ℂ) :
    (center / (v : ℂ) ^ 2).im = center.im / v ^ 2 := by
  rw [show (v : ℂ) ^ 2 = ((v ^ 2 : ℝ) : ℂ) by norm_cast]
  exact Complex.div_ofReal_im center (v ^ 2)

/-- The UV Fourier value at arbitrary nonzero real velocity is
the unit-velocity UV value at rescaled quadratic spectral center.
Both UV values are defined as limits of the same cutoff integral,
so no interchange of limits or arbitrary power-series evaluation
is required. -/
theorem massiveDiracRadialFourierUVCenter_scale_velocity
    (v c : ℝ) (center : ℂ) (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : center.im ≠ 0) :
    massiveDiracRadialFourierUVCenter v c center =
      ((v : ℂ) ^ 2)⁻¹ *
        massiveDiracRadialFourierUVCenter 1 c (center / (v : ℂ) ^ 2) := by
  have hcenter' :
      (center / (v : ℂ) ^ 2).im ≠ 0 := by
    rw [massiveDiracRadial_center_div_velocity_sq_im]
    exact div_ne_zero hcenter (pow_ne_zero 2 hv)
  have hvel := massiveDiracRadialFourier_tendsto_uvValue_center
    v c center hv hc hcenter
  have hunit :
      Filter.Tendsto
        (fun b : ℝ => ∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center / (v : ℂ) ^ 2 - ((p ^ 2 : ℝ) : ℂ))⁻¹)
        Filter.atTop
        (nhds (massiveDiracRadialFourierUVCenter
          1 c (center / (v : ℂ) ^ 2))) := by
    simpa only [one_pow, one_mul] using
      (massiveDiracRadialFourier_tendsto_uvValue_center
        (1 : ℝ) c (center / (v : ℂ) ^ 2)
        (by norm_num) hc hcenter')
  have hscaled :=
    hunit.const_mul (((v : ℂ) ^ 2)⁻¹)
  have heq (b : ℝ) :
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
      ((v : ℂ) ^ 2)⁻¹ *
        (∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center / (v : ℂ) ^ 2 - ((p ^ 2 : ℝ) : ℂ))⁻¹) := by
    simpa only [polarFourierZerothAngularKernel_eq_besselJ] using
      (massiveDiracRadialBesselJ_integral_scale_velocity
        v c b center hv)
  exact tendsto_nhds_unique
    hvel (hscaled.congr' (Filter.Eventually.of_forall fun b => (heq b).symm))

end

end QuantumTheory.Models.MassiveDirac
