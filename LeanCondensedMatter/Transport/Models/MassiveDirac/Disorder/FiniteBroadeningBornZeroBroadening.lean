import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Damping
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-cutoff zero-broadening boundary of the finite-eta Born-Dyson data

This module combines the already-proved real and imaginary fixed-cutoff Born integral limits into a
single complex boundary value and propagates that boundary through the finite-`η` Born-Dyson
energy, mass, and radial denominator.

The external broadening limit is taken at fixed disorder strength and fixed cutoff.  In particular,
the finite real part of the self-energy boundary is retained explicitly; this module does not
identify the result with the damping-only weak-disorder data in `BornPropagator.lean`.

No disorder-strength limit, ultraviolet removal, limit interchange, Hall projection, mechanism
label, SCBA/Ward claim, or exact-disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Complex fixed-cutoff `η → 0⁺` boundary value of the common continuum Born denominator
integral.  Its real part retains the finite logarithmic cutoff dependence while its imaginary part
is the side-indexed metallic on-shell contribution. -/
def finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) : ℂ :=
  ((-(((2 : ℝ) * v ^ 2)⁻¹) *
      (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
        Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖) : ℝ) : ℂ) +
    ((-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi) : ℝ) : ℂ) * Complex.I

/-- The full complex common Born denominator integral converges to its explicit fixed-cutoff
zero-broadening boundary.  This theorem only combines the existing real- and imaginary-part limit
theorems; it does not redo the radial integral analysis. -/
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
        (finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
          side v m probeEnergy pMax)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let reLimit : ℝ :=
    -(((2 : ℝ) * v ^ 2)⁻¹) *
      (Real.log ‖pauliGreenDenominator side v m pMax 0 probeEnergy 0‖ -
        Real.log ‖pauliGreenDenominator side v m 0 0 probeEnergy 0‖)
  let imLimit : ℝ := -(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi)
  have hre : Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).re)
      l (nhds reLimit) := by
    simpa [l, reLimit] using
      (tendsto_finiteCutoffContinuumBornDenominatorIntegral_re_broadening_zero
        side v m probeEnergy pMax hvelocity hmetal hcutoff)
  have him : Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).im)
      l (nhds imLimit) := by
    simpa [l, imLimit] using
      (tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
        side v m probeEnergy pMax hvelocity hmetal hcutoff)
  have hreC : Tendsto
      (fun broadening : ℝ =>
        ((finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).re : ℂ))
      l (nhds (reLimit : ℂ)) :=
    (Complex.continuous_ofReal.tendsto reLimit).comp hre
  have himC : Tendsto
      (fun broadening : ℝ =>
        ((finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).im : ℂ))
      l (nhds (imLimit : ℂ)) :=
    (Complex.continuous_ofReal.tendsto imLimit).comp him
  have hsum := hreC.add (himC.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.I) l (nhds Complex.I)))
  simpa [l, reLimit, imLimit,
    finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary,
    Complex.re_add_im] using hsum

/-- Fixed-cutoff zero-broadening boundary of the scalar continuum Born integral. -/
def finiteCutoffContinuumBornScalarIntegralZeroBroadeningBoundary
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) : ℂ :=
  (probeEnergy : ℂ) *
    finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
      side v m probeEnergy pMax

/-- Fixed-cutoff zero-broadening boundary of the `σ_z` continuum Born integral. -/
def finiteCutoffContinuumBornZIntegralZeroBroadeningBoundary
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) : ℂ :=
  (m : ℂ) *
    finiteCutoffContinuumBornDenominatorIntegralZeroBroadeningBoundary
      side v m probeEnergy pMax

/-- The scalar Born channel converges to the spectral-energy factor times the full complex common
boundary value. -/
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
        (finiteCutoffContinuumBornScalarIntegralZeroBroadeningBoundary
          side v m probeEnergy pMax)) := by
  have hJ := tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
    side v m probeEnergy pMax hvelocity hmetal hcutoff
  have hz : Tendsto
      (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (probeEnergy : ℂ)) := by
    have hcont : ContinuousAt
        (fun broadening : ℝ => spectralParameter side probeEnergy broadening) 0 := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    have hrestricted := hcont.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using hrestricted
  refine (hz.mul hJ).congr' ?_
  filter_upwards with broadening
  exact (finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral
    side v m probeEnergy broadening pMax).symm

/-- The `σ_z` Born channel converges to the mass factor times the full complex common boundary. -/
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
        (finiteCutoffContinuumBornZIntegralZeroBroadeningBoundary
          side v m probeEnergy pMax)) := by
  have hJ := tendsto_finiteCutoffContinuumBornDenominatorIntegral_broadening_zero
    side v m probeEnergy pMax hvelocity hmetal hcutoff
  refine ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (m : ℂ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (m : ℂ))).mul hJ).congr' ?_
  filter_upwards with broadening
  exact (finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral
    side v m probeEnergy broadening pMax).symm

/-- Fixed-cutoff zero-broadening boundary of the scalar continuum Born self-energy coefficient. -/
def finiteCutoffContinuumBornScalarSelfEnergyCoefficientZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornScalarIntegralZeroBroadeningBoundary
      side v m probeEnergy pMax

/-- Fixed-cutoff zero-broadening boundary of the `σ_z` continuum Born self-energy coefficient. -/
def finiteCutoffContinuumBornZSelfEnergyCoefficientZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornZIntegralZeroBroadeningBoundary
      side v m probeEnergy pMax

/-- The finite-`η` scalar self-energy coefficient converges to its full complex fixed-cutoff
boundary at fixed disorder strength. -/
theorem tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornScalarSelfEnergyCoefficient
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornScalarSelfEnergyCoefficientZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hscalar := tendsto_finiteCutoffContinuumBornScalarIntegral_broadening_zero
    side v m probeEnergy pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornScalarSelfEnergyCoefficient,
    finiteCutoffContinuumBornScalarSelfEnergyCoefficientZeroBroadeningBoundary] using
    (tendsto_const_nhds.mul hscalar : Tendsto
      (fun broadening : ℝ =>
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            side v m probeEnergy broadening pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegralZeroBroadeningBoundary
            side v m probeEnergy pMax)))

/-- The finite-`η` `σ_z` self-energy coefficient converges to its full complex fixed-cutoff
boundary at fixed disorder strength. -/
theorem tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornZSelfEnergyCoefficient
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornZSelfEnergyCoefficientZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hz := tendsto_finiteCutoffContinuumBornZIntegral_broadening_zero
    side v m probeEnergy pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornZSelfEnergyCoefficient,
    finiteCutoffContinuumBornZSelfEnergyCoefficientZeroBroadeningBoundary] using
    (tendsto_const_nhds.mul hz : Tendsto
      (fun broadening : ℝ =>
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegral
            side v m probeEnergy broadening pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegralZeroBroadeningBoundary
            side v m probeEnergy pMax)))

/-- Fixed-cutoff zero-broadening boundary of the finite-`η` Born-Dyson effective energy. -/
def finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (probeEnergy : ℂ) -
    finiteCutoffContinuumBornScalarSelfEnergyCoefficientZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax

/-- Fixed-cutoff zero-broadening boundary of the finite-`η` Born-Dyson effective mass. -/
def finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (m : ℂ) +
    finiteCutoffContinuumBornZSelfEnergyCoefficientZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax

/-- The finite-`η` effective spectral energy converges to its full complex fixed-cutoff boundary. -/
theorem tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hz : Tendsto
      (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (probeEnergy : ℂ)) := by
    have hcont : ContinuousAt
        (fun broadening : ℝ => spectralParameter side probeEnergy broadening) 0 := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    have hrestricted := hcont.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using hrestricted
  have hsigma :=
    tendsto_finiteCutoffContinuumBornScalarSelfEnergyCoefficient_broadening_zero
      side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary] using hz.sub hsigma

/-- The finite-`η` effective Dirac mass converges to its full complex fixed-cutoff boundary. -/
theorem tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hsigma :=
    tendsto_finiteCutoffContinuumBornZSelfEnergyCoefficient_broadening_zero
      side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornEffectiveMass,
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary] using
    (tendsto_const_nhds.add hsigma : Tendsto
      (fun broadening : ℝ => (m : ℂ) +
        finiteCutoffContinuumBornZSelfEnergyCoefficient
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((m : ℂ) +
        finiteCutoffContinuumBornZSelfEnergyCoefficientZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)))

/-- Fixed-momentum zero-broadening boundary of the finite-cutoff Born-Dyson quadratic denominator. -/
def finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax ^ 2 -
    ((v ^ 2 * p ^ 2 : ℝ) : ℂ)

/-- At fixed radial momentum, the finite-`η` Born-Dyson denominator converges to the explicit
fixed-cutoff zero-broadening boundary at fixed disorder strength. -/
theorem tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m p probeEnergy disorderStrength hbar pMax)) := by
  have henergy :=
    tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
      side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hmass :=
    tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
      side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have henergySq := henergy.mul henergy
  have hmassSq := hmass.mul hmass
  simpa [finiteCutoffContinuumBornDysonDenominator,
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary, pow_two] using
    (henergySq.sub hmassSq).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => ((v ^ 2 * p ^ 2 : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))

/-- Fixed-cutoff zero-broadening boundary of the radial retarded-advanced Born-Dyson denominator
product consumed by the Hall common-denominator form. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m p probeEnergy disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .advanced v m p probeEnergy disorderStrength hbar pMax

/-- The finite-`η` radial RA denominator product converges at fixed disorder strength to the product
of the separately established retarded and advanced zero-broadening boundaries. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_broadening_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
  have hret := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    .retarded v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hadv := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    .advanced v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct,
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary] using
    hret.mul hadv

end

end QuantumTheory.Transport.Models.MassiveDirac
