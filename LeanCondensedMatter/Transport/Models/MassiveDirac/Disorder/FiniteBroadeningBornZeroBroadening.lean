import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Boundary
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-cutoff zero-broadening boundary of finite-eta Born-Dyson data

This module starts from the common complex Born boundary and propagates it through the finite-`η`
Born-Dyson effective energy and mass and radial denominator. The external broadening limit is taken
at fixed disorder strength and fixed cutoff, retaining the finite real self-energy contribution
explicitly.

No disorder-strength limit, ultraviolet removal, limit interchange, Hall projection, mechanism
label, SCBA/Ward claim, or exact-disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Fixed-cutoff zero-broadening boundary of the finite-`η` Born-Dyson effective energy. -/
def finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (probeEnergy : ℂ) -
    ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
      ((probeEnergy : ℂ) *
        finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax)

/-- Fixed-cutoff zero-broadening boundary of the finite-`η` Born-Dyson effective mass. -/
def finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (m : ℂ) +
    ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
      ((m : ℂ) *
        finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax)

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
  have hsigma :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
      .scalar side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hspectral :
      Tendsto
        (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (probeEnergy : ℂ)) := by
    have hcontinuous :
        ContinuousAt (fun broadening : ℝ => spectralParameter side probeEnergy broadening) 0 := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using
      hcontinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa [finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
    bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator,
    SpectralSide.regulator, spectralParameterOfRegulator] using
    hspectral.sub hsigma

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
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
      .z side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hmass :
      Tendsto (fun _ : ℝ => (m : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (m : ℂ)) := tendsto_const_nhds
  simpa [finiteCutoffContinuumBornEffectiveMass,
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary,
    bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator,
    SpectralSide.regulator] using
    hmass.add hsigma

/-- Fixed-momentum zero-broadening boundary of the finite-cutoff Born-Dyson quadratic denominator. -/
def finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax ^ 2 -
    ((v ^ 2 * p ^ 2 : ℝ) : ℂ)

/-- At fixed radial momentum, the finite-`η` Born-Dyson denominator converges to its explicit
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
  simpa [finiteCutoffContinuumBornDysonDenominator,
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary, pow_two] using
    ((henergy.mul henergy).sub (hmass.mul hmass)).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => ((v ^ 2 * p ^ 2 : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))

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
