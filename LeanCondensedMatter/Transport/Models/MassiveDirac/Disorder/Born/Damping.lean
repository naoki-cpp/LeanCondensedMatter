import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Boundary
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuum Born damping

This module consumes the complex finite-cutoff Born boundary values, projects the scalar and `σ_z`
channels to their damping-generating imaginary parts, then carries them through the physical
continuum prefactor and the upper-band Fermi-surface projection. The resulting positive damping
energy is

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

/-- At fixed finite cutoff beyond the on-shell circle, the `σ_z` Born channel obeys
`Im I_z,s → -sπm/(2v²)` as `η → 0⁺`. This is the imaginary projection of the indexed complex channel
boundary value. -/
theorem tendsto_finiteCutoffContinuumBornZIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornIntegral
          .z side v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)))) := by
  have hcomplex :=
    tendsto_finiteCutoffContinuumBornIntegral_broadening_zero
      .z side v m probeEnergy pMax hvelocity hmetal hcutoff
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  simpa [Function.comp_def, bornSelfEnergyChannelWeight,
    bornSelfEnergyChannelWeightOfRegulator, SpectralSide.regulator, Complex.mul_im] using him

/-- At fixed finite cutoff beyond the on-shell circle, the scalar Born channel obeys
`Im I₀,s → -sπε/(2v²)`. The vanishing regulator cross term is already encoded in the full complex
channel limit, so no separate `ε Im J_s + γ_s Re J_s` bookkeeping is required here. -/
theorem tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornIntegral
          .scalar side v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (probeEnergy *
          (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)))) := by
  have hcomplex :=
    tendsto_finiteCutoffContinuumBornIntegral_broadening_zero
      .scalar side v m probeEnergy pMax hvelocity hmetal hcutoff
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  simpa [Function.comp_def, bornSelfEnergyChannelWeight,
    bornSelfEnergyChannelWeightOfRegulator, SpectralSide.regulator,
    spectralParameterOfRegulator, Complex.mul_im] using him

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
        (finiteCutoffContinuumBornSelfEnergyCoefficient
          .scalar side v m probeEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (probeEnergy *
            (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi))))) := by
  have hcomplex :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
      .scalar side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  simpa [Function.comp_def, bornSelfEnergyChannelWeight,
    bornSelfEnergyChannelWeightOfRegulator, SpectralSide.regulator,
    spectralParameterOfRegulator, Complex.mul_im] using him

/-- At fixed finite cutoff beyond the on-shell circle, the imaginary part of the `σ_z` Pauli
coefficient appearing in the continuum Born self-energy has the side-indexed metallic limit. -/
theorem tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_im_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornSelfEnergyCoefficient
          .z side v m probeEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (m *
            (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi))))) := by
  have hcomplex :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
      .z side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  simpa [Function.comp_def, bornSelfEnergyChannelWeight,
    bornSelfEnergyChannelWeightOfRegulator, SpectralSide.regulator, Complex.mul_im] using him

/-- Retarded continuum Born self-energy projected onto the upper-band Fermi-surface state through
its gauge-independent rank-one projector. -/
noncomputable def finiteCutoffContinuumBornRetardedUpperBandFermiProjection
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator .upper v m (metallicFermiRadius v m fermiEnergy) 0 *
      finiteCutoffContinuumBornSelfEnergy .retarded
        v m fermiEnergy broadening disorderStrength hbar pMax)

/-- At nonzero broadening, the actual upper-band projector trace of the retarded Born self-energy
reduces to the scalar Pauli coefficient plus `m / ε_F` times the `σ_z` coefficient. -/
theorem finiteCutoffContinuumBornRetardedUpperBandFermiProjection_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmF : |m| ≤ fermiEnergy)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornRetardedUpperBandFermiProjection
        v m fermiEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornSelfEnergyCoefficient .scalar .retarded
          v m fermiEnergy broadening disorderStrength hbar pMax +
        (((m / fermiEnergy : ℝ) : ℂ) *
          finiteCutoffContinuumBornSelfEnergyCoefficient .z .retarded
            v m fermiEnergy broadening disorderStrength hbar pMax) := by
  let pF := metallicFermiRadius v m fermiEnergy
  let z : PauliAxis → ℂ
    | .x => 0
    | .y => 0
    | .z => 1
  have hz : sigmaZ = InternalSpace.pauliCombination z := by
    simp [z, InternalSpace.pauliCombination]
  have htraceZ :
      finiteDimensionalOperatorTrace
          (bandProjectorOperator .upper v m pF 0 * matrixOperator sigmaZ) =
        ((m / energy v m pF 0 : ℝ) : ℂ) := by
    change finiteDimensionalOperatorTrace
      ((Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (bandProjector .upper v m pF 0) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaZ) = _
    rw [← map_mul, finiteDimensionalOperatorTrace_toEuclideanCLM,
      bandProjector_eq_pauliCombination, hz, smul_mul_assoc, add_mul, one_mul]
    simp [InternalSpace.trace_pauliCombination_mul_pauliCombination,
      InternalSpace.dotProduct_pauliAxis, diracPauliCoefficients, z]
    ring
  have henergy := energy_metallicFermiRadius v m fermiEnergy hvelocity hmF
  unfold finiteCutoffContinuumBornRetardedUpperBandFermiProjection
  rw [finiteCutoffContinuumBornSelfEnergy_eq .retarded
    v m fermiEnergy broadening disorderStrength hbar pMax hbroadening]
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  simp only [mul_one]
  rw [map_add, map_smul, map_smul]
  change
    finiteDimensionalOperatorTrace (bandProjectorOperator .upper v m pF 0) *
        finiteCutoffContinuumBornSelfEnergyCoefficient .scalar .retarded
          v m fermiEnergy broadening disorderStrength hbar pMax +
      finiteCutoffContinuumBornSelfEnergyCoefficient .z .retarded
          v m fermiEnergy broadening disorderStrength hbar pMax *
        finiteDimensionalOperatorTrace
          (bandProjectorOperator .upper v m pF 0 * matrixOperator sigmaZ) = _
  rw [htraceZ]
  simp [bandProjectorOperator, matrixOperator,
    finiteDimensionalOperatorTrace_toEuclideanCLM, bandProjector_eq_pauliCombination, Matrix.trace]
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
          (finiteCutoffContinuumBornSelfEnergyCoefficient .scalar .retarded
            v m fermiEnergy broadening disorderStrength hbar pMax).im)
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
          (finiteCutoffContinuumBornSelfEnergyCoefficient .z .retarded
            v m fermiEnergy broadening disorderStrength hbar pMax).im)
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
