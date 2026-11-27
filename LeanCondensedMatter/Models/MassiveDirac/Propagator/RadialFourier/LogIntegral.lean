import LeanCondensedMatter.Models.MassiveDirac.Propagator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Fixed-center massive-Dirac radial resolvent logarithm

Exact finite-cutoff radial primitive for arbitrary complex energy and mass,
and the condition under which a pole-free quadratic radial spectral center
must be nonreal. These results use neither Born self-energy nor its
regulator/cutoff limiting procedures.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Exact finite-cutoff radial primitive for a massive-Dirac propagator with
arbitrary complex effective energy and mass. The nonzero imaginary part of
the squared-energy-minus-mass center keeps the whole radial path off the
principal logarithm's branch cut. This extends the clean-regulator Born
primitive to the complex Dyson parameters used by crossed RA diagrams,
without taking any disorder, broadening, or cutoff limit. -/
theorem integral_massiveDiracRadialDenominatorKernel_eq_log
    (v pMax : ℝ) (energy mass : ℂ)
    (hvelocity : v ≠ 0) (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    (∫ p in (0 : ℝ)..pMax,
      massiveDiracRadialDenominatorKernel v p energy mass) =
      -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) *
        (Complex.log (massiveDiracRadialDenominator v pMax energy mass) -
          Complex.log (massiveDiracRadialDenominator v 0 energy mass)) := by
  have hdenIm (p : ℝ) :
      (massiveDiracRadialDenominator v p energy mass).im =
        (energy ^ 2 - mass ^ 2).im := by
    unfold massiveDiracRadialDenominator
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hdenNe (p : ℝ) :
      massiveDiracRadialDenominator v p energy mass ≠ 0 := by
    intro hz
    have hzIm := congrArg Complex.im hz
    rw [hdenIm] at hzIm
    exact hcenter (by simpa using hzIm)
  have hdenCont :
      Continuous (fun p : ℝ => massiveDiracRadialDenominator v p energy mass) := by
    unfold massiveDiracRadialDenominator
    fun_prop
  have hkernelCont :
      Continuous (fun p : ℝ => massiveDiracRadialDenominatorKernel v p energy mass) := by
    unfold massiveDiracRadialDenominatorKernel
    exact (Complex.continuous_ofReal.comp continuous_id).mul
      (hdenCont.inv₀ hdenNe)
  have hdenDeriv (p : ℝ) :
      HasDerivAt
        (fun q : ℝ => massiveDiracRadialDenominator v q energy mass)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) p := by
    have hcomplex :
        HasDerivAt
          (fun z : ℂ => energy ^ 2 - mass ^ 2 - (v : ℂ) ^ 2 * z ^ 2)
          (-2 * (v : ℂ) ^ 2 * (p : ℂ)) (p : ℂ) := by
      convert (hasDerivAt_const (p : ℂ) (energy ^ 2 - mass ^ 2)).sub
          (((hasDerivAt_id (p : ℂ)).pow 2).const_mul ((v : ℂ) ^ 2)) using 1 <;>
        first | rfl | (simp only [id]; ring)
    have hreal := hcomplex.comp_ofReal
    convert hreal using 1
    funext q
    unfold massiveDiracRadialDenominator
    push_cast
    ring
  have hlogDeriv (p : ℝ) :
      HasDerivAt
        (fun q : ℝ => Complex.log (massiveDiracRadialDenominator v q energy mass))
        ((-2 : ℂ) * (v : ℂ) ^ 2 *
          massiveDiracRadialDenominatorKernel v p energy mass) p := by
    have hslit :
        massiveDiracRadialDenominator v p energy mass ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      rw [hdenIm]
      exact hcenter
    have hlog := (hdenDeriv p).clog_real hslit
    convert hlog using 1
    unfold massiveDiracRadialDenominatorKernel
    rw [div_eq_mul_inv]
    ring
  have hint : IntervalIntegrable
      (fun p : ℝ =>
        ((-2 : ℂ) * (v : ℂ) ^ 2) *
          massiveDiracRadialDenominatorKernel v p energy mass)
      volume 0 pMax :=
    (hkernelCont.const_mul ((-2 : ℂ) * (v : ℂ) ^ 2)).intervalIntegrable 0 pMax
  have hmain :
      ((-2 : ℂ) * (v : ℂ) ^ 2) *
          (∫ p in (0 : ℝ)..pMax,
            massiveDiracRadialDenominatorKernel v p energy mass) =
        Complex.log (massiveDiracRadialDenominator v pMax energy mass) -
          Complex.log (massiveDiracRadialDenominator v 0 energy mass) := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun p _ => hlogDeriv p) hint
    rw [← hftc]
    rw [intervalIntegral.integral_const_mul]
  have hv : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvelocity
  have hcoeff : ((-2 : ℂ) * (v : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hv)
  apply mul_left_cancel₀ hcoeff
  rw [hmain]
  field_simp

/-- A pole-free quadratic radial denominator with positive real spectral
parameter has nonzero imaginary part. This uses only the radial pole
parameter, not a particular effective-energy/mass decomposition. -/
theorem massiveDiracRadialCenter_im_ne_zero_of_re_pos
    (v : ℝ) (center : ℂ) (hvelocity : v ≠ 0)
    (hcenterRe : 0 < center.re)
    (hden : ∀ p : ℝ, center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0) :
    center.im ≠ 0 := by
  intro him
  let p : ℝ := Real.sqrt center.re / v
  have hp : v ^ 2 * p ^ 2 = center.re := by
    dsimp [p]
    rw [div_pow, Real.sq_sqrt (le_of_lt hcenterRe)]
    field_simp
  have hzero : center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) = 0 := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re]
      linarith
    · simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im]
        using him
  exact hden p hzero

end

end QuantumTheory.Models.MassiveDirac
