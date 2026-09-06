import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Denominator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-cutoff continuum Born denominator boundary

This module owns the finite-cutoff positive-broadening real boundary of the common massive-Dirac
Born denominator integral.  It stays upstream of channel damping and Born-Dyson consumers.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

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
  have hnorm (p : ℝ) :
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
  have hzeroNormNe :
      ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖ ≠ 0 := by
    simpa using hzeroDen
  have hcutoffNormNe :
      ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ ≠ 0 := by
    simpa using hcutoffDen
  have hlogCutoff := (hnorm pMax).log hcutoffNormNe
  have hlogZero := (hnorm 0).log hzeroNormNe
  have hdiff := hlogCutoff.sub hlogZero
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => -(((2 : ℝ) * v ^ 2)⁻¹))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (-(((2 : ℝ) * v ^ 2)⁻¹)))).mul hdiff).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  have hbroadening_ne : broadening ≠ 0 := ne_of_gt hbroadening
  exact (finiteCutoffContinuumBornDenominatorIntegral_re_eq
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy hbroadening_ne).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
