import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexAngular

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson radial current rung

This module integrates the fixed-radius finite-external-broadening Born-Dyson in-plane rung over
radial momentum. The angular coefficients already contain the full `2π` angle integral, so this
layer attaches only the polar Jacobian `p dp`, one scalar-disorder line, and the physical momentum
measure `momentumMeasurePrefactor hbar`.

The resulting normalized coefficient pair is consumed by the in-plane ladder algebra. Fixed-point
solving and conductivity insertion remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Normalized finite-`η` radial `X` current-rung integrand. The angular `2π` is already included
upstream, so the normalization attaches the scalar-disorder line and `d²p/(2πℏ)²` prefactor exactly
once. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Normalized finite-`η` orientation-sensitive radial `Y` current-rung integrand. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Normalized finite-cutoff finite-`η` `X` coefficient supplied to the in-plane ladder. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Normalized finite-cutoff finite-`η` orientation-sensitive `Y` coefficient supplied to the
in-plane ladder. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
      v m p probeEnergy broadening disorderStrength hbar pMax

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand]

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand]

end

end AnomalousHall.MassiveDirac
