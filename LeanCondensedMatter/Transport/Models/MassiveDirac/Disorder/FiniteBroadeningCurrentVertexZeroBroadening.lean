import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening boundary of the finite-η Born-Dyson current rung

This module propagates the fixed-cutoff Born-Dyson `η → 0⁺` boundary through the pointwise
retarded-advanced angular current-rung coefficients.  The radial integral is deliberately left
untouched: no dominated-convergence or limit-interchange statement is made here.

The repository ordering remains `Gᴿ Γ Gᴬ`, so the orientation-sensitive `Y` numerator keeps the
sign `i (E_A M_R - E_R M_A)` inherited from the finite-`η` rung.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

/-- Fixed-cutoff zero-broadening boundary of the longitudinal angular-rung numerator. -/
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

/-- Fixed-cutoff zero-broadening boundary of the orientation-sensitive angular-rung numerator for
repository ordering `Gᴿ Γ Gᴬ`. -/
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

/-- The longitudinal angular-rung numerator converges pointwise to its fixed-cutoff
zero-broadening boundary. -/
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
  have hretEnergy :=
    tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
      .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hadvEnergy :=
    tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
      .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hretMass :=
    tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
      .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hadvMass :=
    tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
      .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary] using
    (hretEnergy.mul hadvEnergy).sub (hretMass.mul hadvMass)

/-- The orientation-sensitive angular-rung numerator converges pointwise to its fixed-cutoff
zero-broadening boundary without changing the `Gᴿ Γ Gᴬ` orientation convention. -/
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
  have hretEnergy :=
    tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
      .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hadvEnergy :=
    tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
      .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hretMass :=
    tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
      .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hadvMass :=
    tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
      .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hdiff := (hadvEnergy.mul hretMass).sub (hretEnergy.mul hadvMass)
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary] using
    (tendsto_const_nhds.mul hdiff : Tendsto
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
      (nhds
        (Complex.I *
          (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
              .advanced v m probeEnergy disorderStrength hbar pMax *
            finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
              .retarded v m probeEnergy disorderStrength hbar pMax -
          finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
              .retarded v m probeEnergy disorderStrength hbar pMax *
            finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
              .advanced v m probeEnergy disorderStrength hbar pMax))))

/-- Pointwise zero-broadening boundary of the full-angle longitudinal `X` rung coefficient. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax

/-- Pointwise zero-broadening boundary of the full-angle orientation-sensitive `Y` rung
coefficient. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax

/-- At fixed radial momentum, the full-angle longitudinal `X` rung coefficient converges to its
fixed-cutoff zero-broadening boundary whenever the limiting retarded-advanced denominator product
is nonzero. -/
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
  have hnumLimit :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator_broadening_zero
      v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hraw : Tendsto
      (fun broadening : ℝ =>
        (((2 * Real.pi : ℝ) : ℂ)) *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator
            v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
    simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficientZeroBroadeningBoundary]
      using (tendsto_const_nhds.mul (hdenLimit.inv₀ hden)).mul hnumLimit
  refine hraw.congr' ?_
  filter_upwards with broadening
  exact
    (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_eq_denominatorForm
      v m p probeEnergy broadening disorderStrength hbar pMax).symm

/-- At fixed radial momentum, the full-angle orientation-sensitive `Y` rung coefficient converges
to its fixed-cutoff zero-broadening boundary whenever the limiting retarded-advanced denominator
product is nonzero. -/
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
  have hnumLimit :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator_broadening_zero
      v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hraw : Tendsto
      (fun broadening : ℝ =>
        (((2 * Real.pi : ℝ) : ℂ)) *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator
            v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
    simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficientZeroBroadeningBoundary]
      using (tendsto_const_nhds.mul (hdenLimit.inv₀ hden)).mul hnumLimit
  refine hraw.congr' ?_
  filter_upwards with broadening
  exact
    (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_eq_denominatorForm
      v m p probeEnergy broadening disorderStrength hbar pMax).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
