import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening boundary of the finite-eta Born-Dyson current rung

This module propagates the fixed-cutoff, fixed-disorder positive-broadening boundary through every
entry of the retarded-advanced in-plane current-rung matrix at fixed radial momentum. The boundary
RA denominator is assumed nonzero exactly where its inverse is consumed. Coordinate-specific
consumers specialize the direction indices.

No radial-integral limit, solved-ladder limit, disorder-strength limit, ultraviolet removal, Hall
projection, or mechanism label is introduced here. The repository orientation remains `Gᴿ Γ Gᴬ`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Zero-broadening boundary of entry `(i,j)` of the RA angular numerator matrix. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneRotationCoefficient
    (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        .retarded v m probeEnergy disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        .advanced v m probeEnergy disorderStrength hbar pMax -
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
        .retarded v m probeEnergy disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
        .advanced v m probeEnergy disorderStrength hbar pMax)
    (Complex.I *
      (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
          .advanced v m probeEnergy disorderStrength hbar pMax *
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
          .retarded v m probeEnergy disorderStrength hbar pMax -
      finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
          .retarded v m probeEnergy disorderStrength hbar pMax *
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
          .advanced v m probeEnergy disorderStrength hbar pMax))
    i j

/-- Every RA angular numerator entry converges at fixed disorder strength. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator_broadening_zero
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
          i j v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax)) := by
  have hER := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hEA := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hMR := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hMA := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hX := (hER.mul hEA).sub (hMR.mul hMA)
  have hY := ((hEA.mul hMR).sub (hER.mul hMA)).const_mul Complex.I
  cases i <;> cases j
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
      inPlaneRotationCoefficient] using hX
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
      inPlaneRotationCoefficient] using hY.neg
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
      inPlaneRotationCoefficient] using hY
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
      inPlaneRotationCoefficient] using hX

/-- Fixed-`p` zero-broadening boundary of entry `(i,j)` of the RA angular rung matrix. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficientZeroBroadeningBoundary
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
      i j v m probeEnergy disorderStrength hbar pMax

/-- At fixed radial momentum, every angular rung entry converges whenever the boundary RA
denominator product is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_broadening_zero
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          i j v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficientZeroBroadeningBoundary
          i j v m p probeEnergy disorderStrength hbar pMax)) := by
  have hdenLimit :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_broadening_zero
      v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hnum :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator_broadening_zero
      i j v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hclosed :=
    ((hdenLimit.inv₀ hden).const_mul (((2 * Real.pi : ℝ) : ℂ))).mul hnum
  apply Tendsto.congr' ?_ hclosed
  filter_upwards with broadening
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]

/-- Fixed-`p` zero-broadening boundary of normalized current-rung radial entry `(i,j)`. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficientZeroBroadeningBoundary
      i j v m p probeEnergy disorderStrength hbar pMax

/-- Every normalized radial current-rung entry has the corresponding fixed-`p` positive-broadening
boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand_broadening_zero
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
          i j v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
          i j v m p probeEnergy disorderStrength hbar pMax)) := by
  have hcoefficient :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_broadening_zero
      i j v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff hden
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary] using
    hcoefficient.const_mul
      ((((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ))

end

end QuantumTheory.Transport.Models.MassiveDirac
