import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening boundary of the finite-eta Born-Dyson current rung

This module propagates the fixed-cutoff, fixed-disorder positive-broadening boundary through the
orientation-sensitive retarded-advanced current-rung kernel at fixed radial momentum. The boundary
RA denominator is assumed nonzero exactly where its inverse is consumed.

No radial-integral limit, solved-ladder limit, disorder-strength limit, ultraviolet removal, Hall
projection, or mechanism label is introduced here. The repository orientation remains `Gᴿ Γ Gᴬ`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Zero-broadening boundary of the longitudinal RA angular numerator. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      .retarded v m probeEnergy disorderStrength hbar pMax *
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      .advanced v m probeEnergy disorderStrength hbar pMax -
  finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      .retarded v m probeEnergy disorderStrength hbar pMax *
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      .advanced v m probeEnergy disorderStrength hbar pMax

/-- Zero-broadening boundary of the orientation-sensitive RA angular numerator for `Gᴿ Γ Gᴬ`. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  Complex.I *
    (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        .advanced v m probeEnergy disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
        .retarded v m probeEnergy disorderStrength hbar pMax -
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        .retarded v m probeEnergy disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
        .advanced v m probeEnergy disorderStrength hbar pMax)

/-- The longitudinal RA angular numerator converges at fixed disorder strength. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator_broadening_zero
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hER := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hEA := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hMR := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hMA := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary] using
    (hER.mul hEA).sub (hMR.mul hMA)

/-- The orientation-sensitive transverse RA angular numerator converges with the repository
`Gᴿ Γ Gᴬ` sign convention unchanged. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator_broadening_zero
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hER := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hEA := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hMR := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hMA := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hinner := (hEA.mul hMR).sub (hER.mul hMA)
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary] using
    (tendsto_const_nhds.mul hinner : Tendsto
      (fun broadening : ℝ => Complex.I *
        (finiteCutoffContinuumBornEffectiveEnergy
            .advanced v m probeEnergy broadening disorderStrength hbar pMax *
          finiteCutoffContinuumBornEffectiveMass
            .retarded v m probeEnergy broadening disorderStrength hbar pMax -
        finiteCutoffContinuumBornEffectiveEnergy
            .retarded v m probeEnergy broadening disorderStrength hbar pMax *
          finiteCutoffContinuumBornEffectiveMass
            .advanced v m probeEnergy broadening disorderStrength hbar pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Complex.I *
        (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
            .advanced v m probeEnergy disorderStrength hbar pMax *
          finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
            .retarded v m probeEnergy disorderStrength hbar pMax -
        finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
            .retarded v m probeEnergy disorderStrength hbar pMax *
          finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
            .advanced v m probeEnergy disorderStrength hbar pMax))))

/-- Fixed-`p` zero-broadening boundary of the longitudinal RA angular rung coefficient. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax

/-- Fixed-`p` zero-broadening boundary of the orientation-sensitive RA angular rung coefficient. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax

/-- At fixed radial momentum, the longitudinal angular rung coefficient converges whenever the
boundary RA denominator product is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_broadening_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
  have hdenLimit :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_broadening_zero
      v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hnum :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator_broadening_zero
      v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hclosed := (tendsto_const_nhds.mul (hdenLimit.inv₀ hden)).mul hnum
  apply Tendsto.congr' ?_ hclosed
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_eq_denominatorForm]

/-- At fixed radial momentum, the orientation-sensitive angular rung coefficient converges whenever
the boundary RA denominator product is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_broadening_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
  have hdenLimit :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_broadening_zero
      v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hnum :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator_broadening_zero
      v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hclosed := (tendsto_const_nhds.mul (hdenLimit.inv₀ hden)).mul hnum
  apply Tendsto.congr' ?_ hclosed
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_eq_denominatorForm]

/-- Fixed-`p` zero-broadening boundary of the normalized longitudinal current-rung radial integrand. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax

/-- Fixed-`p` zero-broadening boundary of the normalized orientation-sensitive current-rung radial
integrand. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax

/-- The normalized longitudinal radial current-rung integrand has the same fixed-`p` positive-
broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand_broadening_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
          v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
  have hcoefficient :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_broadening_zero
      v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff hden
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary] using
    (tendsto_const_nhds.mul hcoefficient : Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ)) *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ)) *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary
            v m p probeEnergy disorderStrength hbar pMax)))

/-- The normalized orientation-sensitive radial current-rung integrand has the same fixed-`p`
positive-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand_broadening_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
          v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
  have hcoefficient :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_broadening_zero
      v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff hden
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary] using
    (tendsto_const_nhds.mul hcoefficient : Tendsto
      (fun broadening : ℝ =>
        ((((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ)) *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ)) *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary
            v m p probeEnergy disorderStrength hbar pMax)))

end

end QuantumTheory.Transport.Models.MassiveDirac
