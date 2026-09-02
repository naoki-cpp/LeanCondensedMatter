import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorFactorization
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Finite-cutoff evaluation of the continuum Born denominator integral

This module evaluates the shared finite-cutoff radial denominator integral introduced in
`DenominatorFactorization.lean`.  At nonzero probe energy and broadening, the quadratic denominator
stays off the principal-log branch cut for every radial momentum, so its complex logarithm provides
an antiderivative.  For nonzero Dirac velocity this gives the explicit endpoint formula

```text
J_s(pMax) = -(2 v²)⁻¹ [log D_s(pMax) - log D_s(0)].
```

The same finite-cutoff formula separates exactly into a logarithmic norm difference for the real
part and a principal-argument difference for the imaginary part.  The denominator norm is also
exposed as the square root of a real polynomial with quartic cutoff dependence.  The results remain
at finite cutoff and finite nonzero broadening.  No ultraviolet limit, zero-broadening limit,
scattering-rate identification, or renormalization prescription is made.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Radial specialization of the common Green denominator in polynomial form. -/
theorem pauliGreenDenominator_radial_eq
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    pauliGreenDenominator side v m p 0 probeEnergy broadening =
      spectralParameter side probeEnergy broadening ^ 2 - (m : ℂ) ^ 2 -
        (v : ℂ) ^ 2 * (p : ℂ) ^ 2 := by
  unfold pauliGreenDenominator pauliGreenDenominatorOfRegulator energySq spectralParameter
  push_cast
  ring

/-- The radial denominator has real part `ε² - η² - m² - v²p²`, independent of spectral side. -/
@[simp]
theorem pauliGreenDenominator_radial_re
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    (pauliGreenDenominator side v m p 0 probeEnergy broadening).re =
      probeEnergy ^ 2 - broadening ^ 2 - m ^ 2 - v ^ 2 * p ^ 2 := by
  cases side <;>
    simp [pauliGreenDenominator_radial_eq, spectralParameter, SpectralSide.sign, pow_two]

/-- The radial denominator has momentum-independent imaginary part
`2 s ε η`. -/
@[simp]
theorem pauliGreenDenominator_radial_im
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    (pauliGreenDenominator side v m p 0 probeEnergy broadening).im =
      2 * side.sign * probeEnergy * broadening := by
  rw [pauliGreenDenominator_radial_eq]
  simp [spectralParameter, pow_two]
  ring

/-- The squared radial denominator norm is a real polynomial whose cutoff dependence is quartic. -/
theorem pauliGreenDenominator_radial_sq_norm
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    ‖pauliGreenDenominator side v m p 0 probeEnergy broadening‖ ^ 2 =
      (probeEnergy ^ 2 - broadening ^ 2 - m ^ 2 - v ^ 2 * p ^ 2) ^ 2 +
        (2 * probeEnergy * broadening) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [pauliGreenDenominator_radial_re, pauliGreenDenominator_radial_im]
  cases side <;> simp [SpectralSide.sign] <;> ring

/-- The radial denominator norm is the square root of its explicit real polynomial. -/
theorem pauliGreenDenominator_radial_norm_eq_sqrt
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    ‖pauliGreenDenominator side v m p 0 probeEnergy broadening‖ =
      Real.sqrt
        ((probeEnergy ^ 2 - broadening ^ 2 - m ^ 2 - v ^ 2 * p ^ 2) ^ 2 +
          (2 * probeEnergy * broadening) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  rw [pauliGreenDenominator_radial_re, pauliGreenDenominator_radial_im]
  cases side <;> simp [SpectralSide.sign] <;> congr 1 <;> ring

/-- At nonzero probe energy and broadening, the whole radial denominator path lies in the principal
complex-log slit plane. -/
theorem pauliGreenDenominator_radial_mem_slitPlane
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ)
    (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    pauliGreenDenominator side v m p 0 probeEnergy broadening ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [pauliGreenDenominator_radial_im]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (SpectralSide.sign_ne_zero side)) hprobeEnergy)
    hbroadening

/-- The derivative of the quadratic radial denominator is `-2 v² p`. -/
theorem hasDerivAt_pauliGreenDenominator_radial
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    HasDerivAt
      (fun q : ℝ => pauliGreenDenominator side v m q 0 probeEnergy broadening)
      (-2 * (v : ℂ) ^ 2 * (p : ℂ)) p := by
  have hcomplex :
      HasDerivAt
        (fun z : ℂ =>
          spectralParameter side probeEnergy broadening ^ 2 - (m : ℂ) ^ 2 -
            (v : ℂ) ^ 2 * z ^ 2)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) (p : ℂ) := by
    convert (hasDerivAt_const (p : ℂ)
      (spectralParameter side probeEnergy broadening ^ 2 - (m : ℂ) ^ 2)).sub
        (((hasDerivAt_id (p : ℂ)).pow 2).const_mul ((v : ℂ) ^ 2)) using 1 <;>
      first | rfl | (simp only [id]; ring)
  have hreal := hcomplex.comp_ofReal
  convert hreal using 1
  funext q
  exact pauliGreenDenominator_radial_eq side v m probeEnergy broadening q

/-- The principal logarithm of the radial denominator differentiates to `-2v²` times the common
Born radial denominator integrand. -/
theorem hasDerivAt_log_pauliGreenDenominator_radial
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ)
    (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    HasDerivAt
      (fun q : ℝ => Complex.log
        (pauliGreenDenominator side v m q 0 probeEnergy broadening))
      ((-2 : ℂ) * (v : ℂ) ^ 2 *
        continuumBornRadialDenominatorIntegrand side v m probeEnergy broadening p) p := by
  have hlog := (hasDerivAt_pauliGreenDenominator_radial
    side v m probeEnergy broadening p).clog_real
      (pauliGreenDenominator_radial_mem_slitPlane
        side v m probeEnergy broadening p hprobeEnergy hbroadening)
  convert hlog using 1
  unfold continuumBornRadialDenominatorIntegrand
    continuumBornRadialDenominatorIntegrandOfRegulator pauliGreenDenominator
  rw [div_eq_mul_inv]
  ring

private theorem continuous_continuumBornRadialDenominatorIntegrand
    (side : SpectralSide) (v m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    Continuous (continuumBornRadialDenominatorIntegrand
      side v m probeEnergy broadening) := by
  have hden : Continuous (fun p : ℝ =>
      pauliGreenDenominator side v m p 0 probeEnergy broadening) := by
    unfold pauliGreenDenominator pauliGreenDenominatorOfRegulator energySq
      spectralParameterOfRegulator
    fun_prop
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominator side v m p 0 probeEnergy broadening)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominator_ne_zero side v m p 0 probeEnergy broadening hbroadening)
  unfold continuumBornRadialDenominatorIntegrand
    continuumBornRadialDenominatorIntegrandOfRegulator
  exact (Complex.continuous_ofReal.comp continuous_id).mul hinv

/-- Before dividing by `-2v²`, the finite-cutoff denominator integral is exactly the endpoint
principal-log difference. -/
theorem neg_two_mul_velocitySq_mul_finiteCutoffContinuumBornDenominatorIntegral_eq_log_sub_log
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    ((-2 : ℂ) * (v : ℂ) ^ 2) *
        finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax =
      Complex.log (pauliGreenDenominator side v m pMax 0 probeEnergy broadening) -
        Complex.log (pauliGreenDenominator side v m 0 0 probeEnergy broadening) := by
  have hint : IntervalIntegrable
      (fun p : ℝ =>
        ((-2 : ℂ) * (v : ℂ) ^ 2) *
          continuumBornRadialDenominatorIntegrand side v m probeEnergy broadening p)
      volume 0 pMax :=
    ((continuous_continuumBornRadialDenominatorIntegrand
      side v m probeEnergy broadening hbroadening).const_mul
        ((-2 : ℂ) * (v : ℂ) ^ 2)).intervalIntegrable 0 pMax
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hasDerivAt_log_pauliGreenDenominator_radial
      side v m probeEnergy broadening p hprobeEnergy hbroadening) hint
  rw [← hftc]
  unfold finiteCutoffContinuumBornDenominatorIntegral
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator
    continuumBornRadialDenominatorIntegrand
    continuumBornRadialDenominatorIntegrandOfRegulator
  rw [intervalIntegral.integral_const_mul]

/-- Explicit finite-cutoff evaluation of the shared continuum Born denominator integral. -/
theorem finiteCutoffContinuumBornDenominatorIntegral_eq_log_sub_log
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornDenominatorIntegral
        side v m probeEnergy broadening pMax =
      -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) *
        (Complex.log (pauliGreenDenominator side v m pMax 0 probeEnergy broadening) -
          Complex.log (pauliGreenDenominator side v m 0 0 probeEnergy broadening)) := by
  have hmain :=
    neg_two_mul_velocitySq_mul_finiteCutoffContinuumBornDenominatorIntegral_eq_log_sub_log
      side v m probeEnergy broadening pMax hprobeEnergy hbroadening
  have hv : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvelocity
  have hcoeff : ((-2 : ℂ) * (v : ℂ) ^ 2) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hv)
  apply (mul_left_cancel₀ hcoeff)
  rw [hmain]
  field_simp

private theorem continuumBornDenominatorLogPrefactor_eq_ofReal (v : ℝ) :
    -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) =
      ((-(((2 : ℝ) * v ^ 2)⁻¹) : ℝ) : ℂ) := by
  push_cast
  rfl

/-- Exact finite-cutoff real part of the shared denominator integral.  Its endpoint dependence is a
real logarithm of denominator norms; no ultraviolet limit is taken here. -/
theorem finiteCutoffContinuumBornDenominatorIntegral_re_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegral
      side v m probeEnergy broadening pMax).re =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy broadening‖ -
          Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy broadening‖) := by
  rw [finiteCutoffContinuumBornDenominatorIntegral_eq_log_sub_log
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy hbroadening]
  rw [continuumBornDenominatorLogPrefactor_eq_ofReal]
  rw [Complex.re_ofReal_mul]
  simp [Complex.log_re]

/-- Exact finite-cutoff real part with all cutoff dependence exposed through a real polynomial. -/
theorem finiteCutoffContinuumBornDenominatorIntegral_re_eq_log_sqrt_polynomial
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegral
      side v m probeEnergy broadening pMax).re =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        (Real.log
            (Real.sqrt
              ((probeEnergy ^ 2 - broadening ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2) ^ 2 +
                (2 * probeEnergy * broadening) ^ 2)) -
          Real.log
            (Real.sqrt
              ((probeEnergy ^ 2 - broadening ^ 2 - m ^ 2) ^ 2 +
                (2 * probeEnergy * broadening) ^ 2))) := by
  rw [finiteCutoffContinuumBornDenominatorIntegral_re_eq
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy hbroadening]
  rw [pauliGreenDenominator_radial_norm_eq_sqrt]
  rw [pauliGreenDenominator_radial_norm_eq_sqrt]
  simp

/-- Exact finite-cutoff imaginary part of the shared denominator integral.  Its endpoint dependence
is a difference of principal arguments; no zero-broadening or scattering-rate limit is taken here. -/
theorem finiteCutoffContinuumBornDenominatorIntegral_im_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegral
      side v m probeEnergy broadening pMax).im =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        ((pauliGreenDenominator side v m pMax 0 probeEnergy broadening).arg -
          (pauliGreenDenominator side v m 0 0 probeEnergy broadening).arg) := by
  rw [finiteCutoffContinuumBornDenominatorIntegral_eq_log_sub_log
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy hbroadening]
  rw [continuumBornDenominatorLogPrefactor_eq_ofReal]
  rw [Complex.im_ofReal_mul]
  simp [Complex.log_im]

end

end AnomalousHall.MassiveDirac
