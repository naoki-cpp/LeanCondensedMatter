import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorBroadeningLimit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening limits of the continuum Born Pauli channels

At fixed finite cutoff in the positive-energy metallic regime `|m| < ε`, this file propagates the
shared continuum Born denominator limit through the existing exact factorization

```text
I₀,s = z_s J_s,
I_z,s = m J_s,
z_s = ε + s iη.
```

The `σ_z` channel follows directly from `Im J_s`.  The scalar channel additionally contains the
term `s η Re J_s`; its vanishing is proved from a finite fixed-cutoff `η → 0⁺` limit of `Re J_s`,
rather than being discarded formally.  No scattering-rate or lifetime identification is made.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

private theorem finiteCutoffContinuumBornScalarIntegral_im_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    (finiteCutoffContinuumBornScalarIntegral
      side v m probeEnergy broadening pMax).im =
      probeEnergy *
          (finiteCutoffContinuumBornDenominatorIntegral
            side v m probeEnergy broadening pMax).im +
        side.sign * broadening *
          (finiteCutoffContinuumBornDenominatorIntegral
            side v m probeEnergy broadening pMax).re := by
  rw [finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral]
  rw [Complex.mul_im]
  simp [spectralParameter]

private theorem finiteCutoffContinuumBornZIntegral_im_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    (finiteCutoffContinuumBornZIntegral
      side v m probeEnergy broadening pMax).im =
      m *
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).im := by
  rw [finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral]
  rw [Complex.mul_im]
  simp

/-- At fixed finite cutoff beyond the on-shell circle, the real part of the shared denominator
integral has a finite `η → 0⁺` limit.  The endpoint norms remain explicit because this result is used
only to control the scalar-channel cross term; no ultraviolet or renormalization interpretation is
attached to this finite limit. -/
theorem tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
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
      unfold pauliGreenDenominator energySq spectralParameter spectralParameterOfRegulator
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

/-- At fixed finite cutoff beyond the on-shell circle, the `σ_z` Born channel obeys
`Im I_z,s → -sπm/(2v²)` as `η → 0⁺`. -/
theorem tendsto_finiteCutoffContinuumBornZIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornZIntegral
          side v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)))) := by
  have hJ :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
      side v m probeEnergy pMax hvelocity hprobe hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto (fun _ : ℝ => m)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds m)).mul hJ).congr' ?_
  filter_upwards with broadening
  exact (finiteCutoffContinuumBornZIntegral_im_eq
    side v m probeEnergy broadening pMax).symm

/-- At fixed finite cutoff beyond the on-shell circle, the scalar Born channel obeys
`Im I₀,s → -sπε/(2v²)` as `η → 0⁺`.  The proof keeps the exact
`ε Im J_s + sη Re J_s` split and proves the second term vanishes. -/
theorem tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornScalarIntegral
          side v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (probeEnergy *
          (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)))) := by
  have hJim :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
      side v m probeEnergy pMax hvelocity hprobe hmetal hcutoff
  have hJre :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
      side v m probeEnergy pMax hvelocity hprobe hmetal hcutoff
  have hmain := (tendsto_const_nhds : Tendsto (fun _ : ℝ => probeEnergy)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds probeEnergy)).mul hJim
  have heta :
      Tendsto (fun broadening : ℝ => broadening)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hcrossZero :
      Tendsto
        (fun broadening : ℝ =>
          side.sign * broadening *
            (finiteCutoffContinuumBornDenominatorIntegral
              side v m probeEnergy broadening pMax).re)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (((tendsto_const_nhds : Tendsto (fun _ : ℝ => side.sign)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds side.sign)).mul heta).mul hJre)
  have hsum :
      Tendsto
        (fun broadening : ℝ =>
          probeEnergy *
              (finiteCutoffContinuumBornDenominatorIntegral
                side v m probeEnergy broadening pMax).im +
            side.sign * broadening *
              (finiteCutoffContinuumBornDenominatorIntegral
                side v m probeEnergy broadening pMax).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (probeEnergy *
            (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)))) := by
    simpa using hmain.add hcrossZero
  refine hsum.congr' ?_
  filter_upwards with broadening
  exact (finiteCutoffContinuumBornScalarIntegral_im_eq
    side v m probeEnergy broadening pMax).symm

/-- Retarded scalar channel: `Im I₀,R → -πε/(2v²)`. -/
theorem tendsto_finiteCutoffContinuumBornRetardedScalarIntegral_im_broadening_zero
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornScalarIntegral
          .retarded v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (probeEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero
      .retarded v m probeEnergy pMax hvelocity hprobe hmetal hcutoff)

/-- Advanced scalar channel: `Im I₀,A → +πε/(2v²)`. -/
theorem tendsto_finiteCutoffContinuumBornAdvancedScalarIntegral_im_broadening_zero
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornScalarIntegral
          .advanced v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (probeEnergy * (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero
      .advanced v m probeEnergy pMax hvelocity hprobe hmetal hcutoff)

/-- Retarded `σ_z` channel: `Im I_z,R → -πm/(2v²)`. -/
theorem tendsto_finiteCutoffContinuumBornRetardedZIntegral_im_broadening_zero
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornZIntegral
          .retarded v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornZIntegral_im_broadening_zero
      .retarded v m probeEnergy pMax hvelocity hprobe hmetal hcutoff)

/-- Advanced `σ_z` channel: `Im I_z,A → +πm/(2v²)`. -/
theorem tendsto_finiteCutoffContinuumBornAdvancedZIntegral_im_broadening_zero
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornZIntegral
          .advanced v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (m * (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornZIntegral_im_broadening_zero
      .advanced v m probeEnergy pMax hvelocity hprobe hmetal hcutoff)

end

end AnomalousHall.MassiveDirac
