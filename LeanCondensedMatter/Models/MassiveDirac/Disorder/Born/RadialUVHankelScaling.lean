import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVHankelReduction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.RCLike.Sqrt

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

set_option linter.style.header false

/-!
# Principal-branch velocity normalization of the Fourier–Hankel problem

The previous UV Fourier scaling formula includes the real nonzero
velocity. Here we match its exact `v²` normalization against the
principal complex square root in the proposed outgoing Hankel function.
The logarithm cannot pick up a (2πi) shift because multiplication by a
strictly positive real leaves the complex argument unchanged.

As a consequence, the **unit-velocity** upper-half-plane transform
implies the upper-half-plane transform at *every nonzero real velocity*.
The difficult unit-velocity contour/Bessel transform remains a visible
hypothesis; this is not a proof of that integral.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open scoped ComplexConjugate

/-- Scaling the argument by a strictly positive real preserves the
principal square-root branch. Unlike the incorrect unrestricted complex
sqrt-multiplication rule, this holds for every nonzero complex `z`
because the scale is positive real. -/
theorem complexSqrt_div_positiveReal_sq (z : ℂ) (r : ℝ)
    (hr : 0 < r) (hz : z ≠ 0) :
    Complex.sqrt (z / (r : ℂ) ^ 2) =
      Complex.sqrt z / (r : ℂ) := by
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hz' : z / (r : ℂ) ^ 2 ≠ 0 :=
    div_ne_zero hz (pow_ne_zero 2 hrC)
  have hdiv : z / (r : ℂ) ^ 2 =
      z * ((((r⁻¹ : ℝ) ^ 2) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_pow, Complex.ofReal_inv, div_eq_mul_inv, inv_pow]
  have hlog :
      Complex.log (z / (r : ℂ) ^ 2) =
        ((Real.log ((r⁻¹ : ℝ) ^ 2) : ℝ) : ℂ) + Complex.log z := by
    rw [hdiv]
    exact Complex.log_mul_ofReal ((r⁻¹ : ℝ) ^ 2)
      (pow_pos (inv_pos.mpr hr) 2) z hz
  have hlogscale :
      Real.log ((r⁻¹ : ℝ) ^ 2) / 2 = -Real.log r := by
    rw [Real.log_pow, Real.log_inv]
    ring
  have hexpscale :
      Complex.exp ((((Real.log ((r⁻¹ : ℝ) ^ 2) : ℝ) : ℂ) / 2)) =
        (r : ℂ)⁻¹ := by
    calc
      _ = ((Real.exp (Real.log ((r⁻¹ : ℝ) ^ 2) / 2) : ℝ) : ℂ) := by
        simp only [Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_ofNat]
      _ = (((r⁻¹ : ℝ) : ℝ) : ℂ) := by
        rw [hlogscale, Real.exp_neg, Real.exp_log hr]
      _ = (r : ℂ)⁻¹ := by norm_cast
  calc
    Complex.sqrt (z / (r : ℂ) ^ 2) =
        Complex.exp (Complex.log (z / (r : ℂ) ^ 2) / 2) :=
      sqrt_eq_exp hz'
    _ = Complex.exp (((Real.log ((r⁻¹ : ℝ) ^ 2) : ℝ) : ℂ) / 2) *
          Complex.exp (Complex.log z / 2) := by
      rw [hlog, add_div, Complex.exp_add]
    _ = (r : ℂ)⁻¹ * Complex.sqrt z := by
      rw [hexpscale, sqrt_eq_exp hz]
    _ = Complex.sqrt z / (r : ℂ) := by
      rw [div_eq_mul_inv]
      ring

/-- The outgoing candidate scales with velocity exactly as the
original Fourier resolvent does, including the principal square root
and logarithmic Y₀ branch. -/
theorem massiveDiracRadialOutgoingHankelCandidate_scale_velocity
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hcenter : center ≠ 0) :
    massiveDiracRadialOutgoingHankelCandidate v c center =
      ((v : ℂ) ^ 2)⁻¹ *
        massiveDiracRadialOutgoingHankelCandidate
          1 c (center / (v : ℂ) ^ 2) := by
  have hsq : (v : ℂ) ^ 2 = ((|v| : ℝ) : ℂ) ^ 2 := by
    norm_cast
    exact sq_abs v |>.symm
  have harg :
      massiveDiracRadialHankelArgument 1 c
          (center / (v : ℂ) ^ 2) =
        massiveDiracRadialHankelArgument v c center := by
    unfold massiveDiracRadialHankelArgument
    simp only [abs_one, div_one]
    rw [hsq, complexSqrt_div_positiveReal_sq
      center (|v|) (abs_pos.mpr hv) hcenter]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  unfold massiveDiracRadialOutgoingHankelCandidate
  rw [harg]
  simp only [div_eq_mul_inv, Complex.ofReal_one, inv_one, one_pow, mul_one]
  ring

/-- The whole upper-half-plane Fourier–Hankel identification is a
unit-velocity problem: one proof at velocity 1 implies it at all
nonzero real velocities, by exact Fourier scaling and principal-branch
compatibility. This does **not** prove the unit-velocity hypothesis. -/
theorem massiveDiracUpperHalfPlaneHankelTransform_of_unitVelocity
    (v : ℝ) (hv : v ≠ 0)
    (hunit : MassiveDiracUpperHalfPlaneHankelTransform 1) :
    MassiveDiracUpperHalfPlaneHankelTransform v := by
  refine ⟨hv, ?_⟩
  intro radius center hr him
  have hcenter : center ≠ 0 := by
    intro heq
    have hzero := congrArg Complex.im heq
    simp only [Complex.zero_im] at hzero
    exact (ne_of_gt him) hzero
  have hnormalized : 0 < (center / (v : ℂ) ^ 2).im := by
    rw [massiveDiracRadial_center_div_velocity_sq_im]
    exact div_pos him (sq_pos_of_ne_zero hv)
  calc
    massiveDiracRadialFourierUVCenter v radius center =
        ((v : ℂ) ^ 2)⁻¹ *
          massiveDiracRadialFourierUVCenter 1 radius
            (center / (v : ℂ) ^ 2) :=
      massiveDiracRadialFourierUVCenter_scale_velocity
        v radius center hv (ne_of_gt hr) (ne_of_gt him)
    _ = ((v : ℂ) ^ 2)⁻¹ *
          massiveDiracRadialOutgoingHankelCandidate 1 radius
            (center / (v : ℂ) ^ 2) := by
      rw [hunit.2 radius (center / (v : ℂ) ^ 2) hr hnormalized]
    _ = massiveDiracRadialOutgoingHankelCandidate v radius center :=
      (massiveDiracRadialOutgoingHankelCandidate_scale_velocity
        v radius center hv hcenter).symm

end

end QuantumTheory.Models.MassiveDirac
