import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorFactorization
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Finite-cutoff evaluation of the continuum Born denominator integral

This Phase 4 slice evaluates the shared finite-cutoff radial denominator integral introduced in
`DenominatorFactorization.lean`.  At nonzero probe energy and broadening, the quadratic denominator
stays off the principal-log branch cut for every radial momentum, so its complex logarithm provides
an antiderivative.  For nonzero Dirac velocity this gives the explicit endpoint formula

```text
J_s(pMax) = -(2 v²)⁻¹ [log D_s(pMax) - log D_s(0)].
```

The result remains at finite cutoff and finite nonzero broadening.  No ultraviolet limit,
zero-broadening limit, real/imaginary self-energy split, or scattering-rate identification is made.
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
  unfold pauliGreenDenominator energySq
  push_cast
  ring

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
  have hp : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 p :=
    (hasDerivAt_id p).ofReal_comp
  have hp2 : HasDerivAt (fun q : ℝ => (q : ℂ) ^ 2) (2 * (p : ℂ)) p := by
    convert hp.pow 2 using 1 <;> ring
  have hterm :
      HasDerivAt (fun q : ℝ => (v : ℂ) ^ 2 * (q : ℂ) ^ 2)
        ((v : ℂ) ^ 2 * (2 * (p : ℂ))) p :=
    hp2.const_mul ((v : ℂ) ^ 2)
  have hpoly :
      HasDerivAt
        (fun q : ℝ =>
          spectralParameter side probeEnergy broadening ^ 2 - (m : ℂ) ^ 2 -
            (v : ℂ) ^ 2 * (q : ℂ) ^ 2)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) p := by
    convert (hasDerivAt_const p
      (spectralParameter side probeEnergy broadening ^ 2 - (m : ℂ) ^ 2)).sub hterm using 1 <;>
      ring
  convert hpoly using 1
  funext q
  exact (pauliGreenDenominator_radial_eq side v m probeEnergy broadening q).symm

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
  rw [div_eq_mul_inv]
  ring

private theorem continuous_continuumBornRadialDenominatorIntegrand
    (side : SpectralSide) (v m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    Continuous (continuumBornRadialDenominatorIntegrand
      side v m probeEnergy broadening) := by
  have hden : Continuous (fun p : ℝ =>
      pauliGreenDenominator side v m p 0 probeEnergy broadening) := by
    unfold pauliGreenDenominator energySq spectralParameter
    fun_prop
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominator side v m p 0 probeEnergy broadening)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominator_ne_zero side v m p 0 probeEnergy broadening hbroadening)
  unfold continuumBornRadialDenominatorIntegrand
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
  rw [← intervalIntegral.integral_const_mul]
  rfl

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

end

end AnomalousHall.MassiveDirac
