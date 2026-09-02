import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ChannelBroadeningLimit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening damping coefficients of the continuum Born self-energy

This file lifts the already-proved fixed-cutoff `η → 0⁺` limits of the scalar and `σ_z` Born radial
channels through the real disorder/measure prefactor used by `finiteCutoffContinuumBornSelfEnergy`.
It does not introduce a second self-energy definition or new Born integrals.

For

```text
C = disorderStrength * continuumBornAngularMeasurePrefactor hbar,
```

the Pauli coefficients appearing in `finiteCutoffContinuumBornSelfEnergy_eq` obey

```text
Im Σ₀,s → C * [-s π ε / (2v²)],
Im Σ_z,s → C * [-s π m / (2v²)].
```

The physical-momentum measure reduces the common positive magnitude to
`disorderStrength / (4 ℏ² v²)` when `ℏ` and `v` are nonzero.  No scattering time, transport
lifetime, renormalization prescription, or NCA vertex relation is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

private theorem continuumBornScalarSelfEnergyCoefficient_im_eq
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
        finiteCutoffContinuumBornScalarIntegral
          side v m probeEnergy broadening pMax)).im =
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornScalarIntegral
          side v m probeEnergy broadening pMax).im := by
  rw [Complex.im_ofReal_mul]

private theorem continuumBornZSelfEnergyCoefficient_im_eq
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
        finiteCutoffContinuumBornZIntegral
          side v m probeEnergy broadening pMax)).im =
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornZIntegral
          side v m probeEnergy broadening pMax).im := by
  rw [Complex.im_ofReal_mul]

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
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
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
      side v m probeEnergy pMax hvelocity hprobe hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => disorderStrength * continuumBornAngularMeasurePrefactor hbar)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (disorderStrength * continuumBornAngularMeasurePrefactor hbar))).mul hchannel).congr' ?_
  filter_upwards with broadening
  exact (continuumBornScalarSelfEnergyCoefficient_im_eq
    side v m probeEnergy broadening disorderStrength hbar pMax).symm

/-- At fixed finite cutoff beyond the on-shell circle, the imaginary part of the `σ_z` Pauli
coefficient appearing in the continuum Born self-energy has the side-indexed metallic limit. -/
theorem tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_im_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
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
      side v m probeEnergy pMax hvelocity hprobe hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => disorderStrength * continuumBornAngularMeasurePrefactor hbar)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (disorderStrength * continuumBornAngularMeasurePrefactor hbar))).mul hchannel).congr' ?_
  filter_upwards with broadening
  exact (continuumBornZSelfEnergyCoefficient_im_eq
    side v m probeEnergy broadening disorderStrength hbar pMax).symm

/-- Retarded scalar self-energy coefficient: the imaginary part approaches a negative damping
coefficient at positive disorder prefactor. -/
theorem tendsto_finiteCutoffContinuumBornRetardedScalarSelfEnergyCoefficient_im_broadening_zero
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            .retarded v m probeEnergy broadening pMax)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (probeEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_im_broadening_zero
      .retarded v m probeEnergy disorderStrength hbar pMax
      hvelocity hprobe hmetal hcutoff)

/-- Advanced scalar self-energy coefficient: the imaginary part has the opposite sign to the
retarded coefficient. -/
theorem tendsto_finiteCutoffContinuumBornAdvancedScalarSelfEnergyCoefficient_im_broadening_zero
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            .advanced v m probeEnergy broadening pMax)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (probeEnergy * (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi)))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_im_broadening_zero
      .advanced v m probeEnergy disorderStrength hbar pMax
      hvelocity hprobe hmetal hcutoff)

/-- Retarded `σ_z` self-energy coefficient: the imaginary part approaches the corresponding negative
mass-channel damping coefficient. -/
theorem tendsto_finiteCutoffContinuumBornRetardedZSelfEnergyCoefficient_im_broadening_zero
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegral
            .retarded v m probeEnergy broadening pMax)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_im_broadening_zero
      .retarded v m probeEnergy disorderStrength hbar pMax
      hvelocity hprobe hmetal hcutoff)

/-- Advanced `σ_z` self-energy coefficient: the imaginary part has the opposite sign to the
retarded coefficient. -/
theorem tendsto_finiteCutoffContinuumBornAdvancedZSelfEnergyCoefficient_im_broadening_zero
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hprobe : 0 < probeEnergy) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegral
            .advanced v m probeEnergy broadening pMax)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (m * (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi)))) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_im_broadening_zero
      .advanced v m probeEnergy disorderStrength hbar pMax
      hvelocity hprobe hmetal hcutoff)

end

end AnomalousHall.MassiveDirac
