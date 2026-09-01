import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumBorn

set_option linter.style.header false

/-!
# Common denominator factorization for the continuum Born channels

The finite-cutoff massive-Dirac continuum Born closure has two surviving Pauli channels.  Both are
controlled by the same radial denominator integral.  For spectral side `s`, write

```text
J_s(pMax) = ∫₀^{pMax} p dp / D_s(p),
D_s(p) = z_s² - E(p)².
```

Then the existing scalar and `σ_z` channel integrals factor exactly as

```text
I₀,s = z_s J_s,
I_z,s = m J_s.
```

This file only exposes that algebraic factorization.  It does not evaluate `J_s`, take an ultraviolet
or zero-broadening limit, split real and imaginary self-energy parts, or introduce scattering rates.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Common radial denominator integrand, including the polar Jacobian `p`. -/
noncomputable def continuumBornRadialDenominatorIntegrand
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) : ℂ :=
  (p : ℂ) * (pauliGreenDenominator side v m p 0 probeEnergy broadening)⁻¹

/-- The scalar-channel radial integrand is the spectral parameter times the common denominator
integrand. -/
theorem continuumBornRadialScalarIntegrand_eq_spectralParameter_mul_denominatorIntegrand
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    continuumBornRadialScalarIntegrand side v m probeEnergy broadening p =
      spectralParameter side probeEnergy broadening *
        continuumBornRadialDenominatorIntegrand side v m probeEnergy broadening p := by
  unfold continuumBornRadialScalarIntegrand continuumBornRadialDenominatorIntegrand
    pauliGreenScalarCoefficient
  ring

/-- The `σ_z`-channel radial integrand is the mass times the common denominator integrand. -/
theorem continuumBornRadialZIntegrand_eq_mass_mul_denominatorIntegrand
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    continuumBornRadialZIntegrand side v m probeEnergy broadening p =
      (m : ℂ) * continuumBornRadialDenominatorIntegrand
        side v m probeEnergy broadening p := by
  unfold continuumBornRadialZIntegrand continuumBornRadialDenominatorIntegrand
    pauliGreenZCoefficient
  ring

/-- Finite-cutoff interval integral of the common radial denominator integrand. -/
noncomputable def finiteCutoffContinuumBornDenominatorIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialDenominatorIntegrand side v m probeEnergy broadening p

/-- The finite-cutoff scalar Born channel is `z_s` times the common denominator integral. -/
theorem finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    finiteCutoffContinuumBornScalarIntegral side v m probeEnergy broadening pMax =
      spectralParameter side probeEnergy broadening *
        finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax := by
  unfold finiteCutoffContinuumBornScalarIntegral finiteCutoffContinuumBornDenominatorIntegral
  simp_rw [continuumBornRadialScalarIntegrand_eq_spectralParameter_mul_denominatorIntegrand]
  rw [intervalIntegral.integral_const_mul]

/-- The finite-cutoff `σ_z` Born channel is `m` times the common denominator integral. -/
theorem finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    finiteCutoffContinuumBornZIntegral side v m probeEnergy broadening pMax =
      (m : ℂ) * finiteCutoffContinuumBornDenominatorIntegral
        side v m probeEnergy broadening pMax := by
  unfold finiteCutoffContinuumBornZIntegral finiteCutoffContinuumBornDenominatorIntegral
  simp_rw [continuumBornRadialZIntegrand_eq_mass_mul_denominatorIntegrand]
  rw [intervalIntegral.integral_const_mul]

end

end AnomalousHall.MassiveDirac
