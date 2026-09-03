import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexAngular
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.InPlaneLadder

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson radial current rung

This module integrates the fixed-radius finite-external-broadening Born-Dyson in-plane rung over
radial momentum and attaches the continuum scalar-disorder line and physical momentum measure.

The angular coefficients imported from `FiniteBroadeningCurrentVertexAngular.lean` already contain
the full `2π` polar-angle factor.  The radial layer therefore contributes only the polar Jacobian
`p dp`, and the normalized ladder coefficient uses

```text
disorderStrength * momentumMeasurePrefactor hbar
```

exactly once.  In particular, `continuumBornAngularMeasurePrefactor hbar` is not used here because
that would count the angular `2π` a second time.

The resulting normalized coefficient pair is consumed directly by the existing
`inPlaneLadderOperatorAction`; the fixed-point solve, Kubo/Středa insertion, and broadening/disorder
limits remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Finite-`η` radial `X` integrand after the full-angle Born-Dyson reduction, including only the
polar Jacobian `p dp`. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedRadialXIntegrand
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Finite-`η` radial orientation-sensitive `Y` integrand after the full-angle Born-Dyson reduction,
including only the polar Jacobian `p dp`. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedRadialYIntegrand
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Finite-cutoff radial `X` coefficient before the external scalar-disorder line and physical
momentum-measure prefactor are attached. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedRadialXCoefficient
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialXIntegrand
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Finite-cutoff radial orientation-sensitive `Y` coefficient before the external scalar-disorder
line and physical momentum-measure prefactor are attached. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedRadialYCoefficient
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialYIntegrand
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Normalized finite-`η` radial `X` current-rung integrand.  The angular `2π` is already included
upstream, so only the scalar-disorder line and `d²p/(2πℏ)²` prefactor are attached here. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialXIntegrand
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- Normalized finite-`η` radial orientation-sensitive `Y` current-rung integrand. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialYIntegrand
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

/-- The normalized finite-`η` `X` coefficient contains exactly one scalar-disorder factor and one
physical momentum-measure prefactor multiplying the radial Green-product coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_eq_prefactor_mul_radial
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
        v m probeEnergy broadening disorderStrength hbar pMax =
      (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        finiteCutoffContinuumBornDysonRetardedAdvancedRadialXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialXCoefficient
  rw [intervalIntegral.integral_const_mul]

/-- The normalized finite-`η` `Y` coefficient contains exactly one scalar-disorder factor and one
physical momentum-measure prefactor multiplying the radial Green-product coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_eq_prefactor_mul_radial
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
        v m probeEnergy broadening disorderStrength hbar pMax =
      (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        finiteCutoffContinuumBornDysonRetardedAdvancedRadialYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialYCoefficient
  rw [intervalIntegral.integral_const_mul]

/-- Substituting the normalized finite-`η` Born-Dyson coefficients into the canonical in-plane
ladder action gives the repository-oriented rotation `[[X,-Y],[Y,X]]`. -/
theorem finiteCutoffContinuumBornDyson_inPlaneLadderOperatorAction_eq
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) :
    inPlaneLadderOperatorAction
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
        alpha beta =
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax * alpha -
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax * beta) •
          matrixOperator sigmaX +
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax * alpha +
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax * beta) •
          matrixOperator sigmaY := by
  rfl

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedRadialXCoefficient_zero_cutoff
    (v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialXCoefficient
      v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedRadialXCoefficient]

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedRadialYCoefficient_zero_cutoff
    (v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedRadialYCoefficient
      v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedRadialYCoefficient]

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_zero_cutoff
    (v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient]

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_zero_cutoff
    (v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient]

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
