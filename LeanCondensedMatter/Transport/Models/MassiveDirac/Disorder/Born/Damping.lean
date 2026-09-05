import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuum Born damping

This module propagates the finite-cutoff denominator boundary values through the scalar and `σ_z`
Born channels, then through the physical continuum prefactor and the upper-band Fermi-surface
projection. The resulting positive damping energy is

```text
Γ_Born = disorderStrength / (4 ℏ² v²) * (ε_F + m² / ε_F).
```

All limits are fixed-cutoff positive-broadening limits. No lifetime identification, transport
vertex relation, renormalization prescription, or simultaneous ultraviolet / zero-broadening limit
is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- At fixed finite cutoff beyond the on-shell circle, the real part of the shared denominator
integral has a finite `η → 0⁺` limit. The endpoint norms remain explicit because this result is used
only to control the scalar-channel cross term; no ultraviolet or renormalization interpretation is
attached to this finite limit. -/
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

/-- At fixed finite cutoff beyond the on-shell circle, the `σ_z` Born channel obeys
`Im I_z,s → -sπm/(2v²)` as `η → 0⁺`. -/
theorem tendsto_finiteCutoffContinuumBornZIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
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
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto (fun _ : ℝ => m)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds m)).mul hJ).congr' ?_
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral, Complex.mul_im]
  simp

/-- At fixed finite cutoff beyond the on-shell circle, the scalar Born channel obeys
`Im I₀,s → -sπε/(2v²)`. The proof keeps the exact
`ε Im J_s + γ_s Re J_s` split and proves the second term vanishes. -/
theorem tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
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
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hJre :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hmain := (tendsto_const_nhds : Tendsto (fun _ : ℝ => probeEnergy)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds probeEnergy)).mul hJim
  have heta :
      Tendsto (fun broadening : ℝ => broadening)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hregulator :
      Tendsto (fun broadening : ℝ => side.regulator broadening)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [SpectralSide.regulator] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => side.sign)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds side.sign)).mul heta)
  have hcrossZero :
      Tendsto
        (fun broadening : ℝ =>
          side.regulator broadening *
            (finiteCutoffContinuumBornDenominatorIntegral
              side v m probeEnergy broadening pMax).re)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hregulator.mul hJre
  have hsum :
      Tendsto
        (fun broadening : ℝ =>
          probeEnergy *
              (finiteCutoffContinuumBornDenominatorIntegral
                side v m probeEnergy broadening pMax).im +
            side.regulator broadening *
              (finiteCutoffContinuumBornDenominatorIntegral
                side v m probeEnergy broadening pMax).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (probeEnergy *
            (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)))) := by
    simpa using hmain.add hcrossZero
  refine hsum.congr' ?_
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral,
    Complex.mul_im]
  simp [spectralParameter]

/-- The common damping magnitude from the physical-momentum continuum measure simplifies to
`disorderStrength / (4 ℏ² v²)`. -/
theorem continuumBornDampingPrefactor_eq
    (disorderStrength hbar v : ℝ) (hhbar : hbar ≠ 0) (hvelocity : v ≠ 0) :
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) =
      disorderStrength / (4 * hbar ^ 2 * v ^ 2) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold continuumBornAngularMeasurePrefactor momentumMeasurePrefactor
  (field_simp [hhbar, hvelocity, hpi]; ring)

/-- At fixed finite cutoff beyond the on-shell circle, the imaginary part of the scalar Pauli
coefficient appearing in the continuum Born self-energy has the side-indexed metallic limit. -/
theorem tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_im_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            side v m probeEnergy broadening pMax)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (probeEnergy *
            (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi))))) := by
  have hchannel :=
    tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => disorderStrength * continuumBornAngularMeasurePrefactor hbar)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (disorderStrength * continuumBornAngularMeasurePrefactor hbar))).mul hchannel).congr' ?_
  filter_upwards with broadening
  rw [Complex.im_ofReal_mul]

/-- At fixed finite cutoff beyond the on-shell circle, the imaginary part of the `σ_z` Pauli
coefficient appearing in the continuum Born self-energy has the side-indexed metallic limit. -/
theorem tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_im_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegral
            side v m probeEnergy broadening pMax)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (m *
            (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi))))) := by
  have hchannel :=
    tendsto_finiteCutoffContinuumBornZIntegral_im_broadening_zero
      side v m probeEnergy pMax hvelocity hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => disorderStrength * continuumBornAngularMeasurePrefactor hbar)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (disorderStrength * continuumBornAngularMeasurePrefactor hbar))).mul hchannel).congr' ?_
  filter_upwards with broadening
  rw [Complex.im_ofReal_mul]

/-- Retarded continuum Born self-energy projected onto the upper-band Fermi-surface state through
its gauge-independent rank-one projector. -/
noncomputable def finiteCutoffContinuumBornRetardedUpperBandFermiProjection
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator .upper v m (metallicFermiRadius v m fermiEnergy) 0 *
      finiteCutoffContinuumBornSelfEnergy .retarded
        v m fermiEnergy broadening disorderStrength hbar pMax)

private theorem finiteDimensionalOperatorTrace_upperBandProjector_eq_one
    (v m px py : ℝ) :
    finiteDimensionalOperatorTrace
        (bandProjectorOperator .upper v m px py) = (1 : ℂ) := by
  rw [bandProjectorOperator, matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
  simp [bandProjector, Matrix.trace, hamiltonian, sigmaX, sigmaY, sigmaZ]
  ring

private theorem finiteDimensionalOperatorTrace_upperBandProjector_mul_sigmaZ
    (v m px py : ℝ) :
    finiteDimensionalOperatorTrace
        (bandProjectorOperator .upper v m px py * matrixOperator sigmaZ) =
      ((m / energy v m px py : ℝ) : ℂ) := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change finiteDimensionalOperatorTrace
      (φ (bandProjector .upper v m px py) * φ sigmaZ) = _
  rw [← map_mul]
  change finiteDimensionalOperatorTrace
      (matrixOperator (bandProjector .upper v m px py * sigmaZ)) = _
  rw [matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
  simp [bandProjector, Matrix.trace, Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ]
  ring

/-- At nonzero broadening, the actual upper-band projector trace of the retarded Born self-energy
reduces to the scalar Pauli coefficient plus `m / ε_F` times the `σ_z` coefficient. -/
theorem finiteCutoffContinuumBornRetardedUpperBandFermiProjection_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmF : |m| ≤ fermiEnergy)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornRetardedUpperBandFermiProjection
        v m fermiEnergy broadening disorderStrength hbar pMax =
      (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            .retarded v m fermiEnergy broadening pMax) +
        (((m / fermiEnergy : ℝ) : ℂ) *
          (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
            finiteCutoffContinuumBornZIntegral
              .retarded v m fermiEnergy broadening pMax)) := by
  have henergy := energy_metallicFermiRadius v m fermiEnergy hvelocity hmF
  unfold finiteCutoffContinuumBornRetardedUpperBandFermiProjection
  rw [finiteCutoffContinuumBornSelfEnergy_eq .retarded
    v m fermiEnergy broadening disorderStrength hbar pMax hbroadening]
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  simp only [mul_one]
  rw [map_add, map_smul, map_smul]
  rw [finiteDimensionalOperatorTrace_upperBandProjector_eq_one]
  rw [finiteDimensionalOperatorTrace_upperBandProjector_mul_sigmaZ]
  rw [henergy]
  ring

/-- Physical-momentum-measure Born damping energy of the metallic upper band. -/
def continuumBornUpperBandDampingEnergy
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength / (4 * hbar ^ 2 * v ^ 2) *
    (fermiEnergy + m ^ 2 / fermiEnergy)

/-- The upper-band Born damping energy is strictly positive for positive disorder strength in the
strict metallic regime `|m| < εF`. -/
theorem continuumBornUpperBandDampingEnergy_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : 0 < disorderStrength)
    (hmF : |m| < fermiEnergy) :
    0 < continuumBornUpperBandDampingEnergy
      v m fermiEnergy disorderStrength hbar := by
  have hfermi : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hhbarSq : 0 < hbar ^ 2 := sq_pos_of_ne_zero hhbar
  have hvelocitySq : 0 < v ^ 2 := sq_pos_of_ne_zero hvelocity
  have hden : 0 < 4 * hbar ^ 2 * v ^ 2 := by positivity
  have hmassTerm : 0 < fermiEnergy + m ^ 2 / fermiEnergy := by
    have hratio : 0 ≤ m ^ 2 / fermiEnergy :=
      div_nonneg (sq_nonneg m) hfermi.le
    linarith
  unfold continuumBornUpperBandDampingEnergy
  exact mul_pos (div_pos hdisorder hden) hmassTerm

/-- At fixed finite cutoff beyond the upper-band Fermi circle, the projected retarded Born
self-energy has the metallic zero-broadening imaginary limit before simplifying the continuum
measure prefactor. -/
theorem tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_broadening_zero
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmF : |m| < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
          v m fermiEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) *
            (fermiEnergy + m ^ 2 / fermiEnergy)))) := by
  have hfermi : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermi
  have hscalar :
      Tendsto
        (fun broadening : ℝ =>
          ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
            finiteCutoffContinuumBornScalarIntegral
              .retarded v m fermiEnergy broadening pMax)).im)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)))) := by
    simpa [SpectralSide.sign] using
      (tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_im_broadening_zero
        .retarded v m fermiEnergy disorderStrength hbar pMax hvelocity hmF hcutoff)
  have hz :
      Tendsto
        (fun broadening : ℝ =>
          ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
            finiteCutoffContinuumBornZIntegral
              .retarded v m fermiEnergy broadening pMax)).im)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)))) := by
    simpa [SpectralSide.sign] using
      (tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_im_broadening_zero
        .retarded v m fermiEnergy disorderStrength hbar pMax hvelocity hmF hcutoff)
  have hsum := hscalar.add
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => m / fermiEnergy)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (m / fermiEnergy))).mul hz)
  have hprojected :
      Tendsto
        (fun broadening : ℝ =>
          (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
            v m fermiEnergy broadening disorderStrength hbar pMax).im)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
              (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) +
            (m / fermiEnergy) *
              ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
                (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))))) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    rw [finiteCutoffContinuumBornRetardedUpperBandFermiProjection_eq
      v m fermiEnergy broadening disorderStrength hbar pMax
      hvelocity hmF.le (ne_of_gt hbroadening)]
    simp
  have htarget :
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) +
          (m / fermiEnergy) *
            ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
              (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))) =
        -((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) *
            (fermiEnergy + m ^ 2 / fermiEnergy)) := by
    field_simp [hfermiNe]
    ring
  rw [htarget] at hprojected
  exact hprojected

/-- With the physical momentum measure simplified, the projected retarded self-energy approaches
minus the positive Born damping energy. -/
theorem tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_dampingEnergy
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hmF : |m| < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
          v m fermiEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-continuumBornUpperBandDampingEnergy
        v m fermiEnergy disorderStrength hbar)) := by
  have hlimit :=
    tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hvelocity hmF hcutoff
  have hprefactor :=
    continuumBornDampingPrefactor_eq disorderStrength hbar v hhbar hvelocity
  have htarget :
      -((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) *
            (fermiEnergy + m ^ 2 / fermiEnergy)) =
        -continuumBornUpperBandDampingEnergy
          v m fermiEnergy disorderStrength hbar := by
    unfold continuumBornUpperBandDampingEnergy
    rw [hprefactor]
  rw [htarget] at hlimit
  exact hlimit

end

end QuantumTheory.Transport.Models.MassiveDirac
