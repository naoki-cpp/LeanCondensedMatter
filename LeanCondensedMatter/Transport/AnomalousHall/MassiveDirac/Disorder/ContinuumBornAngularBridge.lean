import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.AngularReduction
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ContinuumBorn

set_option linter.style.header false

/-!
# Polar-integral bridge for the finite-cutoff continuum Born self-energy

`ContinuumBorn.lean` packages the radial Born kernel, while `AngularReduction.lean` proves the actual
full-angle integral of the clean Green operator.  This file connects the two layers explicitly.
After multiplying the angular integral by the polar Jacobian `p`, the result is exactly `2π` times
the radial kernel used by the Born calculation.  Integrating over the finite radial interval then
shows that the Born self-energy with prefactor

```text
2π * d²p/(2πℏ)²
```

is identical to the self-energy obtained from the explicit polar-angle integral and the original
physical-momentum measure prefactor.

This closes the derivational gap between momentum inversion and angular reduction.  No UV or
zero-broadening limit is taken here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Radial polar kernel after performing the explicit full angular integral, including the `p`
Jacobian but not the continuum measure prefactor. -/
noncomputable def continuumBornPolarRadialKernel
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  p • continuumAngularGreenIntegral side v m p probeEnergy broadening

/-- The explicit angularly integrated polar kernel is exactly `2π` times the radial kernel used by
`ContinuumBorn.lean`. -/
theorem continuumBornPolarRadialKernel_eq
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    continuumBornPolarRadialKernel side v m probeEnergy broadening p =
      (2 * Real.pi) •
        continuumBornRadialGreenKernel side v m probeEnergy broadening p := by
  rw [continuumBornPolarRadialKernel, continuumAngularGreenIntegral_eq]
  unfold continuumBornRadialGreenKernel
  module

/-- Finite-cutoff radial integral after the angular integral has been carried out explicitly. -/
noncomputable def finiteCutoffContinuumBornPolarGreenIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornPolarRadialKernel side v m probeEnergy broadening p

/-- Explicit angular reduction commutes with the finite radial integration and produces exactly the
factor `2π`. -/
theorem finiteCutoffContinuumBornPolarGreenIntegral_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    finiteCutoffContinuumBornPolarGreenIntegral side v m probeEnergy broadening pMax =
      (2 * Real.pi) •
        finiteCutoffContinuumBornGreenIntegral side v m probeEnergy broadening pMax := by
  unfold finiteCutoffContinuumBornPolarGreenIntegral finiteCutoffContinuumBornGreenIntegral
  simp_rw [continuumBornPolarRadialKernel_eq]
  rw [intervalIntegral.integral_smul]

/-- Continuum Born self-energy written directly from the explicit polar-angle Green integral and the
original physical-momentum measure prefactor `1/(2πℏ)²`. -/
noncomputable def finiteCutoffContinuumBornSelfEnergyFromPolarIntegral
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ) •
    finiteCutoffContinuumBornPolarGreenIntegral side v m probeEnergy broadening pMax

/-- The existing finite-cutoff continuum Born self-energy is exactly the explicit polar-integral
construction.  Thus its `2π` prefactor is derived from angular integration, not postulated from
momentum inversion. -/
theorem finiteCutoffContinuumBornSelfEnergy_eq_polarIntegral
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornSelfEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornSelfEnergyFromPolarIntegral
        side v m probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornSelfEnergyFromPolarIntegral,
    finiteCutoffContinuumBornPolarGreenIntegral_eq]
  unfold finiteCutoffContinuumBornSelfEnergy continuumBornAngularMeasurePrefactor
  rw [← algebraMap_smul ℂ (2 * Real.pi)
    (finiteCutoffContinuumBornGreenIntegral side v m probeEnergy broadening pMax)]
  simp only [RCLike.algebraMap_eq_ofReal, smul_smul]
  congr 1
  push_cast
  ac_rfl

end

end AnomalousHall.MassiveDirac
