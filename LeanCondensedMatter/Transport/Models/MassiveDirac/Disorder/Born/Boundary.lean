import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Denominator

set_option linter.style.header false

/-!
# Complex positive-broadening boundary values for continuum Born transport

This module owns the finite-cutoff metallic `η → 0⁺` boundary values of the continuum Born radial
integrals. The common denominator boundary is packaged as a complex number with its finite real part
and side-indexed imaginary part kept together; the two surviving Born self-energy channels then
inherit one indexed complex boundary theorem before physical damping consumers project concrete
channels to their imaginary parts.

The coordinate-valued denominator limits remain available as analytic ingredients and convenience
APIs. No ultraviolet removal, renormalization prescription, simultaneous limit, or exact
disorder-average claim is introduced here.
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

/-- Complex finite-cutoff metallic boundary value of the common Born denominator integral. The
imaginary component retains the retarded/advanced side through `side.sign`; it is intentionally not
written as the principal logarithm evaluated directly on the negative real axis, where the side of
approach would be lost. -/
noncomputable def finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) : ℂ :=
  ⟨-(((2 : ℝ) * v ^ 2)⁻¹) *
      (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
        Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖),
    -(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)⟩

@[simp]
theorem finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_re
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) :
    (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      side v m probeEnergy pMax).re =
      -(((2 : ℝ) * v ^ 2)⁻¹) *
        (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
          Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖) := by
  rfl

@[simp]
theorem finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) :
    (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      side v m probeEnergy pMax).im =
      -(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi) := by
  rfl

/-- At fixed finite cutoff beyond the on-shell circle, the full complex denominator integral has a
side-indexed metallic `η → 0⁺` boundary value. This is the complex owner of the paired finite real
part and damping-generating imaginary part. -/
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
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax)) := by
  have hre :
      Tendsto
        (fun broadening : ℝ =>
          (finiteCutoffContinuumBornDenominatorIntegral
            side v m probeEnergy broadening pMax).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
            side v m probeEnergy pMax).re) := by
    simpa using
      (tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
        side v m probeEnergy pMax hvelocity hmetal hcutoff)
  have him :
      Tendsto
        (fun broadening : ℝ =>
          (finiteCutoffContinuumBornDenominatorIntegral
            side v m probeEnergy broadening pMax).im)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
            side v m probeEnergy pMax).im) := by
    simpa using
      (tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
        side v m probeEnergy pMax hvelocity hmetal hcutoff)
  have hcomplex :=
    hre.ofReal.add
      (him.ofReal.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.I)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds Complex.I)))
  simpa only [Complex.re_add_im] using hcomplex

private theorem tendsto_bornSelfEnergyChannelWeight_broadening_zero
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (m probeEnergy : ℝ) :
    Tendsto
      (fun broadening : ℝ =>
        bornSelfEnergyChannelWeight channel side m probeEnergy broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bornSelfEnergyChannelWeight channel side m probeEnergy 0)) := by
  cases channel with
  | scalar =>
      have hcontinuous :
          ContinuousAt
            (fun broadening : ℝ =>
              bornSelfEnergyChannelWeight .scalar side m probeEnergy broadening) 0 := by
        unfold bornSelfEnergyChannelWeight bornSelfEnergyChannelWeightOfRegulator
          spectralParameterOfRegulator SpectralSide.regulator
        fun_prop
      exact hcontinuous.tendsto.mono_left inf_le_left
  | z =>
      simpa [bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (m : ℂ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (m : ℂ)))

/-- At fixed finite cutoff beyond the on-shell circle, either surviving Born self-energy channel
converges to its zero-broadening numerator times the common complex denominator boundary value. -/
theorem tendsto_finiteCutoffContinuumBornIntegral_broadening_zero
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornIntegral
          channel side v m probeEnergy broadening pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bornSelfEnergyChannelWeight channel side m probeEnergy 0 *
          finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
            side v m probeEnergy pMax)) := by
  have hJ :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hweight :=
    tendsto_bornSelfEnergyChannelWeight_broadening_zero channel side m probeEnergy
  refine (hweight.mul hJ).congr' ?_
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornIntegral_eq_weight_mul_denominatorIntegral]

/-- The finite-cutoff coefficient of either surviving Born self-energy channel has the corresponding
metallic positive-broadening boundary value. -/
theorem tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornSelfEnergyCoefficient
          channel side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          (bornSelfEnergyChannelWeight channel side m probeEnergy 0 *
            finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
              side v m probeEnergy pMax))) := by
  have hchannel :=
    tendsto_finiteCutoffContinuumBornIntegral_broadening_zero
      channel side v m probeEnergy pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornSelfEnergyCoefficient,
    finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator,
    finiteCutoffContinuumBornIntegral] using
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ))).mul hchannel

end

end QuantumTheory.Transport.Models.MassiveDirac
