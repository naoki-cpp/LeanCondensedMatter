import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Quadratic radial resolvent analysis

Model-independent logarithmic radial primitives and real-axis pole criteria
for a complex quadratic spectral parameter.
-/

namespace QuantumTheory.Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- Quadratic momentum-space resolvent denominator. -/
def quadraticRadialDenominator (v p : ℝ) (center : ℂ) : ℂ :=
  center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)

/-- Polar Jacobian times the quadratic scalar resolvent. -/
def quadraticRadialJacobianKernel (v p : ℝ) (center : ℂ) : ℂ :=
  (p : ℂ) * (quadraticRadialDenominator v p center)⁻¹

/-- The quadratic radial Jacobian integral is a principal-log boundary difference
when the complex pole parameter has nonzero imaginary part. -/
theorem integral_quadraticRadialJacobianKernel_eq_log
    (v pMax : ℝ) (center : ℂ)
    (hvelocity : v ≠ 0) (hcenter : (center).im ≠ 0) :
    (∫ p in (0 : ℝ)..pMax,
      quadraticRadialJacobianKernel v p center) =
      -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) *
        (Complex.log (quadraticRadialDenominator v pMax center) -
          Complex.log (quadraticRadialDenominator v 0 center)) := by
  have hdenIm (p : ℝ) :
      (quadraticRadialDenominator v p center).im =
        (center).im := by
    unfold quadraticRadialDenominator
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hdenNe (p : ℝ) :
      quadraticRadialDenominator v p center ≠ 0 := by
    intro hz
    have hzIm := congrArg Complex.im hz
    rw [hdenIm] at hzIm
    exact hcenter (by simpa using hzIm)
  have hdenCont :
      Continuous (fun p : ℝ => quadraticRadialDenominator v p center) := by
    unfold quadraticRadialDenominator
    fun_prop
  have hkernelCont :
      Continuous (fun p : ℝ => quadraticRadialJacobianKernel v p center) := by
    unfold quadraticRadialJacobianKernel
    exact (Complex.continuous_ofReal.comp continuous_id).mul
      (hdenCont.inv₀ hdenNe)
  have hdenDeriv (p : ℝ) :
      HasDerivAt
        (fun q : ℝ => quadraticRadialDenominator v q center)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) p := by
    have hcomplex :
        HasDerivAt
          (fun z : ℂ => center - (v : ℂ) ^ 2 * z ^ 2)
          (-2 * (v : ℂ) ^ 2 * (p : ℂ)) (p : ℂ) := by
      convert (hasDerivAt_const (p : ℂ) (center)).sub
          (((hasDerivAt_id (p : ℂ)).pow 2).const_mul ((v : ℂ) ^ 2)) using 1 <;>
        first | rfl | (simp only [id]; ring)
    have hreal := hcomplex.comp_ofReal
    convert hreal using 1
    funext q
    unfold quadraticRadialDenominator
    push_cast
    ring
  have hlogDeriv (p : ℝ) :
      HasDerivAt
        (fun q : ℝ => Complex.log (quadraticRadialDenominator v q center))
        ((-2 : ℂ) * (v : ℂ) ^ 2 *
          quadraticRadialJacobianKernel v p center) p := by
    have hslit :
        quadraticRadialDenominator v p center ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      rw [hdenIm]
      exact hcenter
    have hlog := (hdenDeriv p).clog_real hslit
    convert hlog using 1
    unfold quadraticRadialJacobianKernel
    rw [div_eq_mul_inv]
    ring
  have hint : IntervalIntegrable
      (fun p : ℝ =>
        ((-2 : ℂ) * (v : ℂ) ^ 2) *
          quadraticRadialJacobianKernel v p center)
      volume 0 pMax :=
    (hkernelCont.const_mul ((-2 : ℂ) * (v : ℂ) ^ 2)).intervalIntegrable 0 pMax
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hlogDeriv p) hint
  rw [intervalIntegral.integral_const_mul] at hmain
  have hv : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvelocity
  have hcoeff : ((-2 : ℂ) * (v : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hv)
  apply mul_left_cancel₀ hcoeff
  rw [hmain]
  field_simp

/-- A positive-real quadratic pole parameter with no real-axis poles must
have nonzero imaginary part. -/
theorem quadraticRadialDenominator_center_im_ne_zero_of_re_pos
    (v : ℝ) (center : ℂ) (hvelocity : v ≠ 0)
    (hcenterRe : 0 < (center).re)
    (hden : ∀ p : ℝ, quadraticRadialDenominator v p center ≠ 0) :
    (center).im ≠ 0 := by
  intro him
  let p : ℝ := Real.sqrt ((center).re) / v
  have hp : v ^ 2 * p ^ 2 = (center).re := by
    dsimp [p]
    rw [div_pow]
    have hpos : 0 ≤ center.re := le_of_lt hcenterRe
    rw [Real.sq_sqrt hpos]
    field_simp
  have hzero : quadraticRadialDenominator v p center = 0 := by
    apply Complex.ext
    · simp only [quadraticRadialDenominator, Complex.sub_re,
        Complex.ofReal_re, Complex.zero_re]
      exact sub_eq_zero.mpr hp.symm
    · simpa only [quadraticRadialDenominator, Complex.sub_im,
        Complex.ofReal_im, sub_zero, Complex.zero_im] using him
  exact hden p hzero

end

end QuantumTheory.Transport
