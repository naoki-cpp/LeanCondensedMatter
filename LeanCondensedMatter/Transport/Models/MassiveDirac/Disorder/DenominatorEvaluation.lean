import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorFactorization
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Finite-cutoff evaluation of the continuum Born denominator integral

This module evaluates the shared finite-cutoff radial denominator integral introduced in
`DenominatorFactorization.lean`. The analytic owner uses an arbitrary signed regulator `γ`. At
nonzero probe energy and regulator, the quadratic denominator stays off the principal-log branch cut
for every radial momentum, so its complex logarithm provides an antiderivative. For nonzero Dirac
velocity this gives

```text
J(E,γ;pMax) = -(2 v²)⁻¹ [log D(E,γ;pMax) - log D(E,γ;0)].
```

Physical spectral-side real/imaginary formulas are retained only where downstream broadening-limit
analyses consume them. No ultraviolet limit, zero-regulator limit, scattering-rate identification,
or renormalization prescription is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Radial specialization of the arbitrary-regulator Green denominator in polynomial form. -/
theorem pauliGreenDenominatorOfRegulator_radial_eq
    (v m probeEnergy regulator p : ℝ) :
    pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator =
      spectralParameterOfRegulator probeEnergy regulator ^ 2 - (m : ℂ) ^ 2 -
        (v : ℂ) ^ 2 * (p : ℂ) ^ 2 := by
  unfold pauliGreenDenominatorOfRegulator energySq
  push_cast
  ring

/-- The arbitrary-regulator radial denominator has real part
`ε² - γ² - m² - v²p²`. -/
@[simp]
theorem pauliGreenDenominatorOfRegulator_radial_re
    (v m probeEnergy regulator p : ℝ) :
    (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator).re =
      probeEnergy ^ 2 - regulator ^ 2 - m ^ 2 - v ^ 2 * p ^ 2 := by
  rw [pauliGreenDenominatorOfRegulator_radial_eq]
  simp [spectralParameterOfRegulator, pow_two]

/-- The arbitrary-regulator radial denominator has momentum-independent imaginary part `2εγ`. -/
@[simp]
theorem pauliGreenDenominatorOfRegulator_radial_im
    (v m probeEnergy regulator p : ℝ) :
    (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator).im =
      2 * probeEnergy * regulator := by
  rw [pauliGreenDenominatorOfRegulator_radial_eq]
  simp [spectralParameterOfRegulator, pow_two]
  ring

/-- The squared arbitrary-regulator radial denominator norm is an explicit real polynomial. -/
theorem pauliGreenDenominatorOfRegulator_radial_sq_norm
    (v m probeEnergy regulator p : ℝ) :
    ‖pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator‖ ^ 2 =
      (probeEnergy ^ 2 - regulator ^ 2 - m ^ 2 - v ^ 2 * p ^ 2) ^ 2 +
        (2 * probeEnergy * regulator) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [pauliGreenDenominatorOfRegulator_radial_re,
    pauliGreenDenominatorOfRegulator_radial_im]
  ring

/-- The arbitrary-regulator radial denominator norm is the square root of its explicit polynomial. -/
theorem pauliGreenDenominatorOfRegulator_radial_norm_eq_sqrt
    (v m probeEnergy regulator p : ℝ) :
    ‖pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator‖ =
      Real.sqrt
        ((probeEnergy ^ 2 - regulator ^ 2 - m ^ 2 - v ^ 2 * p ^ 2) ^ 2 +
          (2 * probeEnergy * regulator) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  rw [pauliGreenDenominatorOfRegulator_radial_re,
    pauliGreenDenominatorOfRegulator_radial_im]
  congr 1
  ring

/-- Physical-side radial real part, retained for broadening-limit consumers. -/
@[simp]
theorem pauliGreenDenominator_radial_re
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    (pauliGreenDenominator side v m p 0 probeEnergy broadening).re =
      probeEnergy ^ 2 - broadening ^ 2 - m ^ 2 - v ^ 2 * p ^ 2 := by
  cases side <;>
    simp [pauliGreenDenominator, SpectralSide.regulator, SpectralSide.sign]

/-- Physical-side radial imaginary part, retained for broadening-limit consumers. -/
@[simp]
theorem pauliGreenDenominator_radial_im
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    (pauliGreenDenominator side v m p 0 probeEnergy broadening).im =
      2 * side.sign * probeEnergy * broadening := by
  cases side <;>
    simp [pauliGreenDenominator, SpectralSide.regulator, SpectralSide.sign]

/-- At nonzero probe energy and regulator, the radial denominator path lies in the principal-log
slit plane. -/
theorem pauliGreenDenominatorOfRegulator_radial_mem_slitPlane
    (v m probeEnergy regulator p : ℝ)
    (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [pauliGreenDenominatorOfRegulator_radial_im]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hprobeEnergy) hregulator

/-- The derivative of the arbitrary-regulator quadratic radial denominator is `-2 v² p`. -/
theorem hasDerivAt_pauliGreenDenominatorOfRegulator_radial
    (v m probeEnergy regulator p : ℝ) :
    HasDerivAt
      (fun q : ℝ => pauliGreenDenominatorOfRegulator v m q 0 probeEnergy regulator)
      (-2 * (v : ℂ) ^ 2 * (p : ℂ)) p := by
  have hcomplex :
      HasDerivAt
        (fun z : ℂ =>
          spectralParameterOfRegulator probeEnergy regulator ^ 2 - (m : ℂ) ^ 2 -
            (v : ℂ) ^ 2 * z ^ 2)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) (p : ℂ) := by
    convert (hasDerivAt_const (p : ℂ)
      (spectralParameterOfRegulator probeEnergy regulator ^ 2 - (m : ℂ) ^ 2)).sub
        (((hasDerivAt_id (p : ℂ)).pow 2).const_mul ((v : ℂ) ^ 2)) using 1 <;>
      first | rfl | (simp only [id]; ring)
  have hreal := hcomplex.comp_ofReal
  convert hreal using 1
  funext q
  exact pauliGreenDenominatorOfRegulator_radial_eq v m probeEnergy regulator q

/-- The principal logarithm of the arbitrary-regulator radial denominator differentiates to
`-2v²` times the common Born radial denominator integrand. -/
theorem hasDerivAt_log_pauliGreenDenominatorOfRegulator_radial
    (v m probeEnergy regulator p : ℝ)
    (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    HasDerivAt
      (fun q : ℝ => Complex.log
        (pauliGreenDenominatorOfRegulator v m q 0 probeEnergy regulator))
      ((-2 : ℂ) * (v : ℂ) ^ 2 *
        continuumBornRadialDenominatorIntegrandOfRegulator
          v m probeEnergy regulator p) p := by
  have hlog := (hasDerivAt_pauliGreenDenominatorOfRegulator_radial
    v m probeEnergy regulator p).clog_real
      (pauliGreenDenominatorOfRegulator_radial_mem_slitPlane
        v m probeEnergy regulator p hprobeEnergy hregulator)
  convert hlog using 1
  unfold continuumBornRadialDenominatorIntegrandOfRegulator
  rw [div_eq_mul_inv]
  ring

private theorem continuous_continuumBornRadialDenominatorIntegrandOfRegulator
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (continuumBornRadialDenominatorIntegrandOfRegulator
      v m probeEnergy regulator) := by
  have hden : Continuous (fun p : ℝ =>
      pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator) := by
    unfold pauliGreenDenominatorOfRegulator energySq spectralParameterOfRegulator
    fun_prop
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominatorOfRegulator_ne_zero
        v m p 0 probeEnergy regulator hregulator)
  unfold continuumBornRadialDenominatorIntegrandOfRegulator
  exact (Complex.continuous_ofReal.comp continuous_id).mul hinv

/-- Before dividing by `-2v²`, the arbitrary-regulator finite-cutoff denominator integral is the
endpoint principal-log difference. -/
theorem neg_two_mul_velocitySq_mul_finiteCutoffContinuumBornDenominatorIntegralOfRegulator_eq_log_sub_log
    (v m probeEnergy regulator pMax : ℝ)
    (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    ((-2 : ℂ) * (v : ℂ) ^ 2) *
        finiteCutoffContinuumBornDenominatorIntegralOfRegulator
          v m probeEnergy regulator pMax =
      Complex.log
          (pauliGreenDenominatorOfRegulator v m pMax 0 probeEnergy regulator) -
        Complex.log
          (pauliGreenDenominatorOfRegulator v m 0 0 probeEnergy regulator) := by
  have hint : IntervalIntegrable
      (fun p : ℝ =>
        ((-2 : ℂ) * (v : ℂ) ^ 2) *
          continuumBornRadialDenominatorIntegrandOfRegulator
            v m probeEnergy regulator p)
      volume 0 pMax :=
    ((continuous_continuumBornRadialDenominatorIntegrandOfRegulator
      v m probeEnergy regulator hregulator).const_mul
        ((-2 : ℂ) * (v : ℂ) ^ 2)).intervalIntegrable 0 pMax
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hasDerivAt_log_pauliGreenDenominatorOfRegulator_radial
      v m probeEnergy regulator p hprobeEnergy hregulator) hint
  rw [← hftc]
  unfold finiteCutoffContinuumBornDenominatorIntegralOfRegulator
  rw [intervalIntegral.integral_const_mul]

/-- Explicit arbitrary-regulator finite-cutoff evaluation of the shared denominator integral. -/
theorem finiteCutoffContinuumBornDenominatorIntegralOfRegulator_eq_log_sub_log
    (v m probeEnergy regulator pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator
        v m probeEnergy regulator pMax =
      -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) *
        (Complex.log
            (pauliGreenDenominatorOfRegulator v m pMax 0 probeEnergy regulator) -
          Complex.log
            (pauliGreenDenominatorOfRegulator v m 0 0 probeEnergy regulator)) := by
  have hmain :=
    neg_two_mul_velocitySq_mul_finiteCutoffContinuumBornDenominatorIntegralOfRegulator_eq_log_sub_log
      v m probeEnergy regulator pMax hprobeEnergy hregulator
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

/-- Exact arbitrary-regulator finite-cutoff real part of the shared denominator integral. -/
theorem finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_eq
    (v m probeEnergy regulator pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegralOfRegulator
      v m probeEnergy regulator pMax).re =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        (Real.log
            ‖pauliGreenDenominatorOfRegulator v m pMax 0 probeEnergy regulator‖ -
          Real.log
            ‖pauliGreenDenominatorOfRegulator v m 0 0 probeEnergy regulator‖) := by
  rw [finiteCutoffContinuumBornDenominatorIntegralOfRegulator_eq_log_sub_log
    v m probeEnergy regulator pMax hvelocity hprobeEnergy hregulator]
  rw [continuumBornDenominatorLogPrefactor_eq_ofReal]
  rw [Complex.re_ofReal_mul]
  simp [Complex.log_re]

/-- Exact arbitrary-regulator finite-cutoff real part with cutoff dependence exposed through a real
polynomial. -/
theorem finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_eq_log_sqrt_polynomial
    (v m probeEnergy regulator pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegralOfRegulator
      v m probeEnergy regulator pMax).re =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        (Real.log
            (Real.sqrt
              ((probeEnergy ^ 2 - regulator ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2) ^ 2 +
                (2 * probeEnergy * regulator) ^ 2)) -
          Real.log
            (Real.sqrt
              ((probeEnergy ^ 2 - regulator ^ 2 - m ^ 2) ^ 2 +
                (2 * probeEnergy * regulator) ^ 2))) := by
  rw [finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_eq
    v m probeEnergy regulator pMax hvelocity hprobeEnergy hregulator]
  rw [pauliGreenDenominatorOfRegulator_radial_norm_eq_sqrt]
  rw [pauliGreenDenominatorOfRegulator_radial_norm_eq_sqrt]
  simp

/-- Exact arbitrary-regulator finite-cutoff imaginary part of the shared denominator integral. -/
theorem finiteCutoffContinuumBornDenominatorIntegralOfRegulator_im_eq
    (v m probeEnergy regulator pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegralOfRegulator
      v m probeEnergy regulator pMax).im =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        ((pauliGreenDenominatorOfRegulator v m pMax 0 probeEnergy regulator).arg -
          (pauliGreenDenominatorOfRegulator v m 0 0 probeEnergy regulator).arg) := by
  rw [finiteCutoffContinuumBornDenominatorIntegralOfRegulator_eq_log_sub_log
    v m probeEnergy regulator pMax hvelocity hprobeEnergy hregulator]
  rw [continuumBornDenominatorLogPrefactor_eq_ofReal]
  rw [Complex.im_ofReal_mul]
  simp [Complex.log_im]

/-- Physical-side finite-cutoff real part, retained for broadening-limit consumers. -/
theorem finiteCutoffContinuumBornDenominatorIntegral_re_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegral
      side v m probeEnergy broadening pMax).re =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy broadening‖ -
          Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy broadening‖) := by
  simpa [finiteCutoffContinuumBornDenominatorIntegral, pauliGreenDenominator] using
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_eq
      v m probeEnergy (side.regulator broadening) pMax hvelocity hprobeEnergy
        (side.regulator_ne_zero hbroadening)

/-- Physical-side finite-cutoff imaginary part, retained for broadening-limit consumers. -/
theorem finiteCutoffContinuumBornDenominatorIntegral_im_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    (finiteCutoffContinuumBornDenominatorIntegral
      side v m probeEnergy broadening pMax).im =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        ((pauliGreenDenominator side v m pMax 0 probeEnergy broadening).arg -
          (pauliGreenDenominator side v m 0 0 probeEnergy broadening).arg) := by
  simpa [finiteCutoffContinuumBornDenominatorIntegral, pauliGreenDenominator] using
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator_im_eq
      v m probeEnergy (side.regulator broadening) pMax hvelocity hprobeEnergy
        (side.regulator_ne_zero hbroadening)

end

end AnomalousHall.MassiveDirac
