import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.SelfEnergy.Core

/-!
# Common radial denominator integral for continuum Born self-energy

Factorization of the two isotropic Born self-energy channels through a common scalar radial
denominator integral, with arbitrary-regulator and physical-side variants.
-/

set_option linter.style.header false

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Common radial denominator integrand at an arbitrary signed regulator, including the polar
Jacobian `p`. -/
noncomputable def continuumBornRadialDenominatorIntegrandOfRegulator
    (v m probeEnergy regulator p : ℝ) : ℂ :=
  massiveDiracRadialDenominatorKernel v p
    (spectralParameterOfRegulator probeEnergy regulator) (m : ℂ)

/-- Either surviving Born self-energy radial integrand is its channel numerator times the common
denominator integrand. -/
private theorem continuumBornRadialIntegrandOfRegulator_eq_weight_mul_denominatorIntegrand
    (channel : BornSelfEnergyChannel) (v m probeEnergy regulator p : ℝ) :
    continuumBornRadialIntegrandOfRegulator channel v m probeEnergy regulator p =
      bornSelfEnergyChannelWeightOfRegulator channel m probeEnergy regulator *
        continuumBornRadialDenominatorIntegrandOfRegulator
          v m probeEnergy regulator p := by
  cases channel <;>
    simp [continuumBornRadialIntegrandOfRegulator,
      bornSelfEnergyChannelWeightOfRegulator,
      continuumBornRadialDenominatorIntegrandOfRegulator,
      massiveDiracRadialDenominatorKernel, massiveDiracRadialDenominator,
      pauliGreenScalarCoefficientOfRegulator,
      pauliGreenPauliCoefficientOfRegulator, pauliGreenDenominatorOfRegulator,
      energySq, InternalSpace.pauliAxisComponent] <;>
    ring

/-- Finite-cutoff interval integral of the common radial denominator integrand at an arbitrary
signed regulator. -/
noncomputable def finiteCutoffContinuumBornDenominatorIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialDenominatorIntegrandOfRegulator
      v m probeEnergy regulator p

/-- Physical-side common denominator integral. -/
noncomputable def finiteCutoffContinuumBornDenominatorIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornDenominatorIntegralOfRegulator
    v m probeEnergy (side.regulator broadening) pMax

/-- Arbitrary-regulator factorization of either surviving Born self-energy channel. -/
private theorem finiteCutoffContinuumBornIntegralOfRegulator_eq_weight_mul_denominatorIntegral
    (channel : BornSelfEnergyChannel) (v m probeEnergy regulator pMax : ℝ) :
    finiteCutoffContinuumBornIntegralOfRegulator
        channel v m probeEnergy regulator pMax =
      bornSelfEnergyChannelWeightOfRegulator channel m probeEnergy regulator *
        finiteCutoffContinuumBornDenominatorIntegralOfRegulator
          v m probeEnergy regulator pMax := by
  unfold finiteCutoffContinuumBornIntegralOfRegulator
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator
  simp_rw [continuumBornRadialIntegrandOfRegulator_eq_weight_mul_denominatorIntegrand]
  rw [intervalIntegral.integral_const_mul]

/-- Physical-side factorization of either surviving Born self-energy channel. -/
theorem finiteCutoffContinuumBornIntegral_eq_weight_mul_denominatorIntegral
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening pMax : ℝ) :
    finiteCutoffContinuumBornIntegral channel side v m probeEnergy broadening pMax =
      bornSelfEnergyChannelWeight channel side m probeEnergy broadening *
        finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax := by
  simpa [finiteCutoffContinuumBornIntegral, bornSelfEnergyChannelWeight,
    finiteCutoffContinuumBornDenominatorIntegral] using
    finiteCutoffContinuumBornIntegralOfRegulator_eq_weight_mul_denominatorIntegral
      channel v m probeEnergy (side.regulator broadening) pMax

end

end QuantumTheory.Models.MassiveDirac
