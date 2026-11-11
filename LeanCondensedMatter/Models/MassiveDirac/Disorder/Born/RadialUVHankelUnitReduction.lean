import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVUnitVelocity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.RCLike.Sqrt

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
        simp only [Complex.ofReal_div, Complex.ofReal_exp]
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
  simp only [one_pow, div_one]
  simp only [div_eq_mul_inv]
  ring

/-- The whole upper-half-plane Fourier–Hankel identification is a
unit-velocity problem: one proof at velocity 1 implies it at all
nonzero real velocities, by exact Fourier scaling and principal-branch
compatibility. This does **not** prove the unit-velocity hypothesis. -/
theorem massiveDiracUpperHalfPlaneHankelTransform_of_unitVelocity
    (v : ℝ) (hv : v ≠ 0)
    (hunit : MassiveDiracUpperHalfPlaneHankelTransform 1) :
    MassiveDiracUpperHalfPlaneHankelTransform v := by
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
      rw [hunit radius (center / (v : ℂ) ^ 2) hr hnormalized]
    _ = massiveDiracRadialOutgoingHankelCandidate v radius center :=
      (massiveDiracRadialOutgoingHankelCandidate_scale_velocity
        v radius center hv hcenter).symm

end

end QuantumTheory.Models.MassiveDirac
