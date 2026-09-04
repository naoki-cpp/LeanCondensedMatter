import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuum Born denominator analysis

This module owns the exact finite-cutoff evaluation of the common massive-Dirac Born denominator,
its fixed-regulator ultraviolet behavior, and its positive-broadening boundary values. The analytic
calculation is stated at arbitrary signed regulator where possible; physical spectral-side limits
are introduced only where the branch orientation matters.

The exact finite-cutoff integral is expressed through the principal complex logarithm. At fixed
nonzero regulator its real part has the logarithmic ultraviolet divergence, while at fixed finite
cutoff in the metallic regime its imaginary part has the retarded/advanced `η → 0⁺` boundary value.
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
  rw [← pauliGreenDenominatorOfRegulator_radial_sq_norm,
    Real.sqrt_sq (norm_nonneg _)]

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
  unfold continuumBornRadialDenominatorIntegrandOfRegulator
  exact (Complex.continuous_ofReal.comp continuous_id).mul
    (continuous_inv_pauliGreenDenominatorOfRegulator_radial
      v m probeEnergy regulator hregulator)

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

set_option linter.style.header false

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

private theorem tendsto_continuumBornRadialNormPolynomial_atTop
    (v m probeEnergy regulator : ℝ) (hvelocity : v ≠ 0) :
    Tendsto
      (fun p : ℝ =>
        (probeEnergy ^ 2 - regulator ^ 2 - m ^ 2 - v ^ 2 * p ^ 2) ^ 2 +
          (2 * probeEnergy * regulator) ^ 2)
      atTop atTop := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hvelocity
  have hp2 : Tendsto (fun p : ℝ => p ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hlead : Tendsto (fun p : ℝ => v ^ 2 * p ^ 2) atTop atTop :=
    hp2.const_mul_atTop hv2
  have hshift :
      Tendsto
        (fun p : ℝ => v ^ 2 * p ^ 2 -
          (probeEnergy ^ 2 - regulator ^ 2 - m ^ 2))
        atTop atTop := by
    convert tendsto_atTop_add_const_right atTop
      (-(probeEnergy ^ 2 - regulator ^ 2 - m ^ 2)) hlead using 1
    funext p
    ring
  have hsq :
      Tendsto
        (fun p : ℝ =>
          (v ^ 2 * p ^ 2 -
            (probeEnergy ^ 2 - regulator ^ 2 - m ^ 2)) ^ 2)
        atTop atTop := by
    simpa [pow_two] using hshift.atTop_mul_atTop₀ hshift
  convert tendsto_atTop_add_const_right atTop
    ((2 * probeEnergy * regulator) ^ 2) hsq using 1
  funext p
  ring

/-- For nonzero Dirac velocity, the arbitrary-regulator radial Green denominator norm diverges at
large momentum. -/
theorem tendsto_pauliGreenDenominatorOfRegulator_radial_norm_atTop
    (v m probeEnergy regulator : ℝ) (hvelocity : v ≠ 0) :
    Tendsto
      (fun p : ℝ =>
        ‖pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator‖)
      atTop atTop := by
  simpa [Function.comp_def, pauliGreenDenominatorOfRegulator_radial_norm_eq_sqrt] using
    Real.tendsto_sqrt_atTop.comp
      (tendsto_continuumBornRadialNormPolynomial_atTop
        v m probeEnergy regulator hvelocity)

/-- The logarithm carrying the cutoff dependence of the arbitrary-regulator Born denominator real
part tends to `+∞`. -/
theorem tendsto_log_pauliGreenDenominatorOfRegulator_radial_norm_atTop
    (v m probeEnergy regulator : ℝ) (hvelocity : v ≠ 0) :
    Tendsto
      (fun p : ℝ => Real.log
        ‖pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator‖)
      atTop atTop := by
  simpa [Function.comp_def] using
    Real.tendsto_log_atTop.comp
      (tendsto_pauliGreenDenominatorOfRegulator_radial_norm_atTop
        v m probeEnergy regulator hvelocity)

/-- At fixed finite nonzero signed regulator, the exact continuum Born denominator real part has a
logarithmic ultraviolet divergence to `-∞`. -/
theorem tendsto_finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_atTop
    (v m probeEnergy regulator : ℝ)
    (hvelocity : v ≠ 0) (hprobeEnergy : probeEnergy ≠ 0) (hregulator : regulator ≠ 0) :
    Tendsto
      (fun pMax : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegralOfRegulator
          v m probeEnergy regulator pMax).re)
      atTop atBot := by
  have hlog := tendsto_log_pauliGreenDenominatorOfRegulator_radial_norm_atTop
    v m probeEnergy regulator hvelocity
  have hdiff :
      Tendsto
        (fun pMax : ℝ =>
          Real.log
              ‖pauliGreenDenominatorOfRegulator v m pMax 0 probeEnergy regulator‖ -
            Real.log
              ‖pauliGreenDenominatorOfRegulator v m 0 0 probeEnergy regulator‖)
        atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop
        (-Real.log
          ‖pauliGreenDenominatorOfRegulator v m 0 0 probeEnergy regulator‖) hlog
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hvelocity
  have hcoeff : -(((2 : ℝ) * v ^ 2)⁻¹) < 0 := by
    exact neg_lt_zero.mpr (inv_pos.mpr (mul_pos (by norm_num) hv2))
  refine ((tendsto_const_mul_atBot_of_neg hcoeff).2 hdiff).congr'
    (Eventually.of_forall fun pMax => ?_)
  exact (finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_eq
    v m probeEnergy regulator pMax hvelocity hprobeEnergy hregulator).symm

end

end AnomalousHall.MassiveDirac

set_option linter.style.header false

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

private theorem mass_sq_lt_probe_sq
    (m probeEnergy : ℝ) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy) :
    m ^ 2 < probeEnergy ^ 2 := by
  rw [← sq_abs m]
  nlinarith [abs_nonneg m]

private theorem tendsto_pauliGreenDenominator_radial_broadening_zero
    (side : SpectralSide) (v m probeEnergy p : ℝ) :
    Tendsto
      (fun broadening : ℝ => pauliGreenDenominator side v m p 0 probeEnergy broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (pauliGreenDenominator side v m p 0 probeEnergy 0)) := by
  have hcontinuous :
      ContinuousAt
        (fun broadening : ℝ => pauliGreenDenominator side v m p 0 probeEnergy broadening) 0 := by
    unfold pauliGreenDenominator pauliGreenDenominatorOfRegulator energySq
      spectralParameterOfRegulator SpectralSide.regulator
    fun_prop
  exact hcontinuous.tendsto.mono_left inf_le_left

private theorem tendsto_arg_pauliGreenDenominator_zero_radial_broadening_zero
    (side : SpectralSide) (v m probeEnergy : ℝ)
    (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        (pauliGreenDenominator side v m 0 0 probeEnergy broadening).arg)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmetalSq := mass_sq_lt_probe_sq m probeEnergy hprobe hmetal
  have hre : 0 < (pauliGreenDenominator side v m 0 0 probeEnergy 0).re := by
    rw [pauliGreenDenominator_radial_re]
    nlinarith
  have him : (pauliGreenDenominator side v m 0 0 probeEnergy 0).im = 0 := by
    rw [pauliGreenDenominator_radial_im]
    simp
  have hslit : pauliGreenDenominator side v m 0 0 probeEnergy 0 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hre
  have harg :=
    (Complex.continuousAt_arg hslit).tendsto.comp
      (tendsto_pauliGreenDenominator_radial_broadening_zero side v m probeEnergy 0)
  have hargZero : (pauliGreenDenominator side v m 0 0 probeEnergy 0).arg = 0 := by
    rw [Complex.arg_eq_zero_iff]
    exact ⟨hre.le, him⟩
  rw [hargZero] at harg
  exact harg

private theorem tendsto_arg_pauliGreenDenominator_cutoff_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hprobe : 0 < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (pauliGreenDenominator side v m pMax 0 probeEnergy broadening).arg)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (side.sign * Real.pi)) := by
  have hre : (pauliGreenDenominator side v m pMax 0 probeEnergy 0).re < 0 := by
    rw [pauliGreenDenominator_radial_re]
    nlinarith
  have him : (pauliGreenDenominator side v m pMax 0 probeEnergy 0).im = 0 := by
    rw [pauliGreenDenominator_radial_im]
    simp
  have hden := tendsto_pauliGreenDenominator_radial_broadening_zero
    side v m probeEnergy pMax
  cases side with
  | retarded =>
      have hwithin :
          Tendsto
            (fun broadening : ℝ =>
              pauliGreenDenominator .retarded v m pMax 0 probeEnergy broadening)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhdsWithin
              (pauliGreenDenominator .retarded v m pMax 0 probeEnergy 0)
              {z : ℂ | 0 ≤ z.im}) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hden, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
        rw [pauliGreenDenominator_radial_im]
        simp only [SpectralSide.sign_retarded]
        nlinarith [mul_pos hprobe hbroadening]
      have harg :=
        (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hwithin
      simpa [Function.comp_def, SpectralSide.sign] using harg
  | advanced =>
      have hwithin :
          Tendsto
            (fun broadening : ℝ =>
              pauliGreenDenominator .advanced v m pMax 0 probeEnergy broadening)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhdsWithin
              (pauliGreenDenominator .advanced v m pMax 0 probeEnergy 0)
              {z : ℂ | z.im < 0}) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hden, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
        rw [pauliGreenDenominator_radial_im]
        simp only [SpectralSide.sign_advanced]
        nlinarith [mul_pos hprobe hbroadening]
      have harg :=
        (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp hwithin
      simpa [Function.comp_def, SpectralSide.sign] using harg

/-- At fixed finite cutoff beyond the on-shell circle, `Im J_s → -sπ/(2v²)` as `η → 0⁺`. -/
theorem tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi))) := by
  have hprobeEnergy : probeEnergy ≠ 0 := ne_of_gt hprobe
  have hargCutoff := tendsto_arg_pauliGreenDenominator_cutoff_broadening_zero
    side v m probeEnergy pMax hprobe hcutoff
  have hargZero := tendsto_arg_pauliGreenDenominator_zero_radial_broadening_zero
    side v m probeEnergy hprobe hmetal
  have hdiff :
      Tendsto
        (fun broadening : ℝ =>
          (pauliGreenDenominator side v m pMax 0 probeEnergy broadening).arg -
            (pauliGreenDenominator side v m 0 0 probeEnergy broadening).arg)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (side.sign * Real.pi)) := by
    simpa using hargCutoff.sub hargZero
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => -(((2 : ℝ) * v ^ 2)⁻¹))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (-(((2 : ℝ) * v ^ 2)⁻¹)))).mul hdiff).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  have hbroadening_ne : broadening ≠ 0 := ne_of_gt hbroadening
  exact (finiteCutoffContinuumBornDenominatorIntegral_im_eq
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy hbroadening_ne).symm

end

end MassiveDirac
end AnomalousHall
