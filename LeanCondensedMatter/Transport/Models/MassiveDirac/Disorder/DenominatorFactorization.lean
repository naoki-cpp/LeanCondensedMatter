import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumBorn

set_option linter.style.header false

/-!
# Common denominator factorization for the continuum Born channels

The analytic owner is the finite-cutoff massive-Dirac continuum Born closure at an arbitrary signed
regulator `γ`. Both surviving Pauli channels are controlled by the same radial denominator integral,

```text
J(E,γ;pMax) = ∫₀^{pMax} p dp / D(E,γ;p),
D(E,γ;p) = z(E,γ)² - E(p)²,
```

with `I₀ = z J` and `I_z = m J`. Physical spectral-side statements are retained as thin
specializations where downstream broadening-limit code consumes them.

This file does not evaluate `J`, take an ultraviolet or zero-broadening limit, split real and
imaginary self-energy parts, or introduce scattering rates.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Common radial denominator integrand at an arbitrary signed regulator, including the polar
Jacobian `p`. -/
noncomputable def continuumBornRadialDenominatorIntegrandOfRegulator
    (v m probeEnergy regulator p : ℝ) : ℂ :=
  (p : ℂ) *
    (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator)⁻¹

/-- The arbitrary-regulator scalar radial integrand is the spectral parameter times the common
denominator integrand. -/
theorem continuumBornRadialScalarIntegrandOfRegulator_eq_spectralParameter_mul_denominatorIntegrand
    (v m probeEnergy regulator p : ℝ) :
    continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p =
      spectralParameterOfRegulator probeEnergy regulator *
        continuumBornRadialDenominatorIntegrandOfRegulator
          v m probeEnergy regulator p := by
  unfold continuumBornRadialScalarIntegrandOfRegulator
    continuumBornRadialDenominatorIntegrandOfRegulator
    pauliGreenScalarCoefficientOfRegulator
  ring

/-- The arbitrary-regulator `σ_z` radial integrand is the mass times the common denominator
integrand. -/
theorem continuumBornRadialZIntegrandOfRegulator_eq_mass_mul_denominatorIntegrand
    (v m probeEnergy regulator p : ℝ) :
    continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p =
      (m : ℂ) * continuumBornRadialDenominatorIntegrandOfRegulator
        v m probeEnergy regulator p := by
  unfold continuumBornRadialZIntegrandOfRegulator
    continuumBornRadialDenominatorIntegrandOfRegulator
    pauliGreenZCoefficientOfRegulator
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

/-- Arbitrary-regulator scalar Born channel factorization. -/
theorem finiteCutoffContinuumBornScalarIntegralOfRegulator_eq_spectralParameter_mul_denominatorIntegral
    (v m probeEnergy regulator pMax : ℝ) :
    finiteCutoffContinuumBornScalarIntegralOfRegulator
        v m probeEnergy regulator pMax =
      spectralParameterOfRegulator probeEnergy regulator *
        finiteCutoffContinuumBornDenominatorIntegralOfRegulator
          v m probeEnergy regulator pMax := by
  unfold finiteCutoffContinuumBornScalarIntegralOfRegulator
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator
  simp_rw [continuumBornRadialScalarIntegrandOfRegulator_eq_spectralParameter_mul_denominatorIntegrand]
  rw [intervalIntegral.integral_const_mul]

/-- Arbitrary-regulator `σ_z` Born channel factorization. -/
theorem finiteCutoffContinuumBornZIntegralOfRegulator_eq_mass_mul_denominatorIntegral
    (v m probeEnergy regulator pMax : ℝ) :
    finiteCutoffContinuumBornZIntegralOfRegulator
        v m probeEnergy regulator pMax =
      (m : ℂ) * finiteCutoffContinuumBornDenominatorIntegralOfRegulator
        v m probeEnergy regulator pMax := by
  unfold finiteCutoffContinuumBornZIntegralOfRegulator
    finiteCutoffContinuumBornDenominatorIntegralOfRegulator
  simp_rw [continuumBornRadialZIntegrandOfRegulator_eq_mass_mul_denominatorIntegrand]
  rw [intervalIntegral.integral_const_mul]

/-- Physical-side scalar channel factorization, retained for downstream broadening-limit consumers. -/
theorem finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    finiteCutoffContinuumBornScalarIntegral side v m probeEnergy broadening pMax =
      spectralParameter side probeEnergy broadening *
        finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax := by
  simpa [finiteCutoffContinuumBornScalarIntegral,
    finiteCutoffContinuumBornDenominatorIntegral, spectralParameter] using
    finiteCutoffContinuumBornScalarIntegralOfRegulator_eq_spectralParameter_mul_denominatorIntegral
      v m probeEnergy (side.regulator broadening) pMax

/-- Physical-side `σ_z` channel factorization, retained for downstream broadening-limit consumers. -/
theorem finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    finiteCutoffContinuumBornZIntegral side v m probeEnergy broadening pMax =
      (m : ℂ) * finiteCutoffContinuumBornDenominatorIntegral
        side v m probeEnergy broadening pMax := by
  simpa [finiteCutoffContinuumBornZIntegral,
    finiteCutoffContinuumBornDenominatorIntegral] using
    finiteCutoffContinuumBornZIntegralOfRegulator_eq_mass_mul_denominatorIntegral
      v m probeEnergy (side.regulator broadening) pMax

end

end AnomalousHall.MassiveDirac
