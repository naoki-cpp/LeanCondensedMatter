import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Denominator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-cutoff continuum Born zero-broadening boundary

This module owns the fixed-cutoff positive-broadening boundary of the common massive-Dirac Born
denominator integral and propagates it only through the existing scalar and `σ_z` channel
factorizations.  Channel damping and Born-Dyson dressing remain downstream.

The real boundary retains its finite logarithmic cutoff dependence.  No ultraviolet removal,
disorder-strength limit, renormalization prescription, or simultaneous limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

private theorem tendsto_pauliGreenDenominator_radial_norm_broadening_zero
    (side : SpectralSide) (v m probeEnergy p : ℝ) :
    Tendsto
      (fun broadening : ℝ =>
        ‖pauliGreenDenominator side v m p 0 probeEnergy broadening‖)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ‖pauliGreenDenominator side v m p 0 probeEnergy 0‖) := by
  have hcontinuous :
      ContinuousAt
        (fun broadening : ℝ =>
          ‖pauliGreenDenominator side v m p 0 probeEnergy broadening‖) 0 := by
    unfold pauliGreenDenominator pauliGreenDenominatorOfRegulator energySq
      spectralParameterOfRegulator SpectralSide.regulator
    fun_prop
  exact hcontinuous.tendsto.mono_left inf_le_left

/-- At fixed finite cutoff beyond the on-shell circle, the real part of the shared denominator
integral has a finite `η → 0⁺` limit. The endpoint norms remain explicit; no ultraviolet or
renormalization interpretation is attached to this finite limit. -/
theorem tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-(((2 : ℝ) * v ^ 2)⁻¹) *
          (Real.log
              ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
            Real.log
              ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖))) := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hprobeEnergy : probeEnergy ≠ 0 := ne_of_gt hprobe
  have hmetalSq : m ^ 2 < probeEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hzeroRe :
      0 < (pauliGreenDenominator side v m 0 0 probeEnergy 0).re := by
    rw [pauliGreenDenominator_radial_re]
    nlinarith
  have hcutoffRe :
      (pauliGreenDenominator side v m pMax 0 probeEnergy 0).re < 0 := by
    rw [pauliGreenDenominator_radial_re]
    nlinarith
  have hzeroDen :
      pauliGreenDenominator side v m 0 0 probeEnergy 0 ≠ 0 := by
    intro hzero
    have hre :
        (pauliGreenDenominator side v m 0 0 probeEnergy 0).re = 0 := by
      simpa using congrArg Complex.re hzero
    linarith
  have hcutoffDen :
      pauliGreenDenominator side v m pMax 0 probeEnergy 0 ≠ 0 := by
    intro hzero
    have hre :
        (pauliGreenDenominator side v m pMax 0 probeEnergy 0).re = 0 := by
      simpa using congrArg Complex.re hzero
    linarith
  have hlogCutoff :=
    (tendsto_pauliGreenDenominator_radial_norm_broadening_zero
      side v m probeEnergy pMax).log (by simpa using hcutoffDen)
  have hlogZero :=
    (tendsto_pauliGreenDenominator_radial_norm_broadening_zero
      side v m probeEnergy 0).log (by simpa using hzeroDen)
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => -(((2 : ℝ) * v ^ 2)⁻¹))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (-(((2 : ℝ) * v ^ 2)⁻¹)))).mul (hlogCutoff.sub hlogZero)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  exact (finiteCutoffContinuumBornDenominatorIntegral_re_eq
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy
      (ne_of_gt hbroadening)).symm

/-- Complex fixed-cutoff `η → 0⁺` boundary value of the common continuum Born denominator
integral. Its real part retains the finite logarithmic cutoff dependence and its imaginary part is
the side-indexed metallic on-shell contribution. -/
def finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) : ℂ :=
  ((-(((2 : ℝ) * v ^ 2)⁻¹) *
      (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
        Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖) : ℝ) : ℂ) +
    ((-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi) : ℝ) : ℂ) * Complex.I

/-- The full complex common Born denominator integral converges to its explicit fixed-cutoff
zero-broadening boundary. This only combines the separately proved real and imaginary limits. -/
theorem tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
          side v m probeEnergy pMax)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let reLimit : ℝ :=
    -(((2 : ℝ) * v ^ 2)⁻¹) *
      (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
        Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖)
  let imLimit : ℝ := -(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)
  have hre : Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).re)
      l (nhds reLimit) := by
    simpa [l, reLimit] using
      (tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
        side v m probeEnergy pMax hvelocity hmetal hcutoff)
  have him : Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).im)
      l (nhds imLimit) := by
    simpa [l, imLimit] using
      (tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
        side v m probeEnergy pMax hvelocity hmetal hcutoff)
  have hreC := (Complex.continuous_ofReal.tendsto reLimit).comp hre
  have himC := (Complex.continuous_ofReal.tendsto imLimit).comp him
  have hsum := hreC.add (himC.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.I) l (nhds Complex.I)))
  simpa [l, reLimit, imLimit,
    finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary,
    Complex.re_add_im] using hsum

private theorem tendsto_spectralParameter_broadening_zero
    (side : SpectralSide) (probeEnergy : ℝ) :
    Tendsto
      (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (probeEnergy : ℂ)) := by
  have hcontinuous :
      ContinuousAt
        (fun broadening : ℝ => spectralParameter side probeEnergy broadening) 0 := by
    unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
    fun_prop
  simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using
    hcontinuous.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)

/-- The scalar Born channel inherits the full complex zero-broadening boundary from `I₀ = z J`. -/
theorem tendsto_finiteCutoffContinuumBornScalarIntegral_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornScalarIntegral
          side v m probeEnergy broadening pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((probeEnergy : ℂ) *
          finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
            side v m probeEnergy pMax)) := by
  have hJ := tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
    side v m probeEnergy pMax hvelocity hmetal hcutoff
  refine ((tendsto_spectralParameter_broadening_zero side probeEnergy).mul hJ).congr' ?_
  filter_upwards with broadening
  exact (finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral
    side v m probeEnergy broadening pMax).symm

/-- The `σ_z` Born channel inherits the full complex zero-broadening boundary from `I_z = m J`. -/
theorem tendsto_finiteCutoffContinuumBornZIntegral_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornZIntegral
          side v m probeEnergy broadening pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((m : ℂ) *
          finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
            side v m probeEnergy pMax)) := by
  have hJ := tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
    side v m probeEnergy pMax hvelocity hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (m : ℂ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (m : ℂ))).mul hJ).congr' ?_
  filter_upwards with broadening
  exact (finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral
    side v m probeEnergy broadening pMax).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
