import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorEvaluation
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.header false

/-!
# Ultraviolet behavior of the continuum Born denominator integral

This module isolates the large-cutoff behavior of the exact finite-regulator real part of the shared
massive-Dirac continuum Born denominator integral. The analytic owner uses an arbitrary signed
regulator `γ`. The quartic real denominator polynomial tends to `+∞`; consequently the radial
denominator norm and its real logarithm tend to `+∞`. Since the exact real part carries the negative
prefactor `-(2v²)⁻¹`, it tends to `-∞` for nonzero Dirac velocity.

The regulator remains fixed and nonzero throughout the final theorem. No zero-regulator limit,
interchange of ultraviolet and regulator limits, renormalization prescription, scattering rate,
SCBA/NCA, or exact-disorder-average claim is made here.
-/

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
  have hpoly := tendsto_continuumBornRadialNormPolynomial_atTop
    v m probeEnergy regulator hvelocity
  have hsqrt := Real.tendsto_sqrt_atTop.comp hpoly
  refine hsqrt.congr' (Eventually.of_forall fun p => ?_)
  exact (pauliGreenDenominatorOfRegulator_radial_norm_eq_sqrt
    v m probeEnergy regulator p).symm

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
