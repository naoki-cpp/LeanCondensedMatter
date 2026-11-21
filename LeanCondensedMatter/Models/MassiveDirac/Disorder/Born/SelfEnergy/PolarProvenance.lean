import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.SelfEnergy.Core

/-!
# Explicit polar-angle provenance for continuum Born self-energy

The full angular Green integral produces exactly the expected factor `2π` and connects
the physical disorder/measure prefactor to the finite-cutoff radial Green integral.
All declarations in this module were moved unchanged from the original SelfEnergy module.
-/

set_option linter.style.header false

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Radial polar kernel after performing the explicit full angular integral, including the `p`
Jacobian but not the continuum measure prefactor. -/
private noncomputable def continuumBornPolarRadialKernelOfRegulator
    (v m probeEnergy regulator p : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  p • continuumAngularGreenIntegralOfRegulator v m p probeEnergy regulator

/-- The explicit angularly integrated polar kernel is exactly `2π` times the radial kernel used by
the continuum Born self-energy. -/
private theorem continuumBornPolarRadialKernelOfRegulator_eq
    (v m probeEnergy regulator p : ℝ) :
    continuumBornPolarRadialKernelOfRegulator v m probeEnergy regulator p =
      (2 * Real.pi) •
        continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p := by
  rw [continuumBornPolarRadialKernelOfRegulator,
    continuumAngularGreenIntegralOfRegulator_eq]
  unfold continuumBornRadialGreenKernelOfRegulator
  module

/-- Finite-cutoff radial integral after the angular integral has been carried out explicitly. -/
private noncomputable def finiteCutoffContinuumBornPolarGreenIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornPolarRadialKernelOfRegulator v m probeEnergy regulator p

/-- Explicit angular reduction commutes with the finite radial integration and produces exactly the
factor `2π`. -/
private theorem finiteCutoffContinuumBornPolarGreenIntegralOfRegulator_eq
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
canonical external disorder-line × physical-momentum-measure prefactor. -/
private noncomputable def finiteCutoffContinuumBornSelfEnergyFromPolarIntegralOfRegulator
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ) •
    finiteCutoffContinuumBornPolarGreenIntegralOfRegulator
      v m probeEnergy regulator pMax

end

end QuantumTheory.Models.MassiveDirac
