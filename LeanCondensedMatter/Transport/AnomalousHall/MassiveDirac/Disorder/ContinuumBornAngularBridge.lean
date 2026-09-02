import LeanCondensedMatter.Transport.Models.MassiveDirac.AngularReduction
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumBorn

set_option linter.style.header false

/-!
# Polar-integral bridge for the finite-cutoff continuum Born self-energy

`ContinuumBorn.lean` packages the radial Born kernel, while `AngularReduction.lean` proves the actual
full-angle integral of the clean Green operator. Both are owned at an arbitrary signed regulator
`γ`. After multiplying the angular integral by the polar Jacobian `p`, the result is exactly `2π`
times the radial kernel used by the Born calculation. Integrating over the finite radial interval
then identifies the arbitrary-regulator Born self-energy with the explicit polar-angle construction.

This closes the derivational gap between momentum inversion and angular reduction. No UV or
zero-broadening limit is taken here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Radial polar kernel after performing the explicit full angular integral, including the `p`
Jacobian but not the continuum measure prefactor. -/
noncomputable def continuumBornPolarRadialKernelOfRegulator
    (v m probeEnergy regulator p : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  p • continuumAngularGreenIntegralOfRegulator v m p probeEnergy regulator

/-- The explicit angularly integrated polar kernel is exactly `2π` times the radial kernel used by
`ContinuumBorn.lean`. -/
theorem continuumBornPolarRadialKernelOfRegulator_eq
    (v m probeEnergy regulator p : ℝ) :
    continuumBornPolarRadialKernelOfRegulator v m probeEnergy regulator p =
      (2 * Real.pi) •
        continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p := by
  rw [continuumBornPolarRadialKernelOfRegulator,
    continuumAngularGreenIntegralOfRegulator_eq]
  unfold continuumBornRadialGreenKernelOfRegulator
  module

/-- Finite-cutoff radial integral after the angular integral has been carried out explicitly. -/
noncomputable def finiteCutoffContinuumBornPolarGreenIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornPolarRadialKernelOfRegulator v m probeEnergy regulator p

/-- Explicit angular reduction commutes with the finite radial integration and produces exactly the
factor `2π`. -/
theorem finiteCutoffContinuumBornPolarGreenIntegralOfRegulator_eq
    (v m probeEnergy regulator pMax : ℝ) :
    finiteCutoffContinuumBornPolarGreenIntegralOfRegulator
        v m probeEnergy regulator pMax =
      (2 * Real.pi) •
        finiteCutoffContinuumBornGreenIntegralOfRegulator
          v m probeEnergy regulator pMax := by
  unfold finiteCutoffContinuumBornPolarGreenIntegralOfRegulator
    finiteCutoffContinuumBornGreenIntegralOfRegulator
  simp_rw [continuumBornPolarRadialKernelOfRegulator_eq]
  rw [intervalIntegral.integral_smul]

/-- Continuum Born self-energy written directly from the explicit polar-angle Green integral and the
original physical-momentum measure prefactor `1/(2πℏ)²`. -/
noncomputable def finiteCutoffContinuumBornSelfEnergyFromPolarIntegralOfRegulator
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ) •
    finiteCutoffContinuumBornPolarGreenIntegralOfRegulator
      v m probeEnergy regulator pMax

/-- The arbitrary-regulator finite-cutoff continuum Born self-energy is exactly the explicit
polar-integral construction, so its `2π` prefactor is derived from angular integration. -/
theorem finiteCutoffContinuumBornSelfEnergyOfRegulator_eq_polarIntegral
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornSelfEnergyOfRegulator
        v m probeEnergy regulator disorderStrength hbar pMax =
      finiteCutoffContinuumBornSelfEnergyFromPolarIntegralOfRegulator
        v m probeEnergy regulator disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornSelfEnergyFromPolarIntegralOfRegulator,
    finiteCutoffContinuumBornPolarGreenIntegralOfRegulator_eq]
  unfold finiteCutoffContinuumBornSelfEnergyOfRegulator continuumBornAngularMeasurePrefactor
  rw [← algebraMap_smul ℂ (2 * Real.pi)
    (finiteCutoffContinuumBornGreenIntegralOfRegulator
      v m probeEnergy regulator pMax)]
  simp only [RCLike.algebraMap_eq_ofReal, smul_smul]
  congr 1
  push_cast
  simp [mul_assoc, mul_comm, mul_left_comm]

end

end AnomalousHall.MassiveDirac
