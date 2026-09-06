import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Damping

set_option linter.style.header false

/-!
# Complex positive-broadening boundary values for continuum Born transport

This module packages the finite-cutoff metallic `η → 0⁺` boundary values of the continuum Born
radial integrals as complex limits. The canonical denominator boundary value keeps its finite real
part and side-indexed imaginary part together; scalar and `σ_z` channel limits are then obtained by
ordinary complex multiplication before physical consumers project to real or imaginary parts.

The existing coordinate-valued limit theorems remain available as physical convenience APIs. No
ultraviolet removal, renormalization prescription, simultaneous limit, or exact disorder-average
claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

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
  have hre :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have him :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hcomplex :=
    hre.ofReal.add
      (him.ofReal.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.I)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds Complex.I)))
  have htarget :
      (((-(((2 : ℝ) * v ^ 2)⁻¹) *
          (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
            Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖) : ℝ) : ℂ) +
        ((-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi) : ℝ) : ℂ) * Complex.I =
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
        side v m probeEnergy pMax := by
    apply Complex.ext <;>
      simp [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue]
  rw [← htarget]
  simpa only [Complex.re_add_im] using hcomplex

/-- The full `σ_z` Born radial integral converges as a complex number to `m` times the common
complex denominator boundary value. -/
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
          finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
            side v m probeEnergy pMax)) := by
  have hJ :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hm :
      Tendsto (fun _ : ℝ => (m : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (m : ℂ)) := tendsto_const_nhds
  refine (hm.mul hJ).congr' ?_
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral]

/-- The full scalar Born radial integral converges as a complex number to `ε` times the common
complex denominator boundary value. The vanishing regulator cross term is absorbed automatically by
complex multiplication rather than split into separate real/imaginary bookkeeping. -/
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
          finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
            side v m probeEnergy pMax)) := by
  have hJ :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hspectral :
      Tendsto
        (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (probeEnergy : ℂ)) := by
    have hcontinuous :
        ContinuousAt (fun broadening : ℝ => spectralParameter side probeEnergy broadening) 0 := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    have hlimit :
        Tendsto
          (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (spectralParameter side probeEnergy 0)) :=
      hcontinuous.tendsto.mono_left inf_le_left
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using hlimit
  refine (hspectral.mul hJ).congr' ?_
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral]

/-- Complex scalar-channel coefficient of the finite-cutoff Born self-energy has the metallic
positive-broadening boundary value obtained by multiplying the scalar radial boundary by the common
continuum prefactor. -/
theorem tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            side v m probeEnergy broadening pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          ((probeEnergy : ℂ) *
            finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
              side v m probeEnergy pMax))) := by
  have hchannel :=
    tendsto_finiteCutoffContinuumBornScalarIntegral_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  exact (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ))).mul hchannel

/-- Complex `σ_z`-channel coefficient of the finite-cutoff Born self-energy has the metallic
positive-broadening boundary value obtained by multiplying the `σ_z` radial boundary by the common
continuum prefactor. -/
theorem tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegral
            side v m probeEnergy broadening pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          ((m : ℂ) *
            finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
              side v m probeEnergy pMax))) := by
  have hchannel :=
    tendsto_finiteCutoffContinuumBornZIntegral_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  exact (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ))).mul hchannel

end

end QuantumTheory.Transport.Models.MassiveDirac
