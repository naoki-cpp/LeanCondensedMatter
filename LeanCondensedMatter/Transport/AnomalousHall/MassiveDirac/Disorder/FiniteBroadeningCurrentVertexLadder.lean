import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson ladder specialization

This module specializes the canonical two-component in-plane ladder solution to the normalized
finite-cutoff finite-external-broadening Born-Dyson rung coefficients.  It introduces no second
fixed-point algebra: the determinant, solved coefficients, and bounded solved vertex are direct
specializations of `InPlaneLadder.lean`.

The repository orientation remains `Gᴿ Γ Gᴬ`, so the transverse coefficient has the same sign as the
normalized radial `Y` coefficient.  Physical charge-current conversion and Kubo/Středa insertion
remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Determinant of `I - L` for the normalized finite-`η` Born-Dyson in-plane current rung. -/
noncomputable def finiteCutoffContinuumBornDysonLadderDeterminant
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderDeterminant
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- Solved longitudinal coefficient of the normalized finite-`η` Born-Dyson current vertex. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderSolvedXCoefficient
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- Solved orientation-sensitive transverse coefficient of the normalized finite-`η` Born-Dyson
current vertex. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderSolvedYCoefficient
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- Bounded dimensionless in-plane current vertex obtained by solving the normalized finite-`η`
Born-Dyson ladder. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedVertex
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedVertex
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- The model-specific solved vertex has the canonical solved `σₓ`/`σᵧ` coefficients. -/
theorem finiteCutoffContinuumBornDysonLadderSolvedVertex_eq
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedVertex
        v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaX +
        finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaY := by
  rfl

/-- The normalized finite-`η` Born-Dyson vertex solves `Γ = σₓ + L(Γ)` exactly whenever the
specialized two-component determinant is nonzero. -/
theorem finiteCutoffContinuumBornDysonLadderSolvedVertex_fixedPoint
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminant
      v m probeEnergy broadening disorderStrength hbar pMax ≠ 0) :
    finiteCutoffContinuumBornDysonLadderSolvedVertex
        v m probeEnergy broadening disorderStrength hbar pMax =
      matrixOperator sigmaX +
        inPlaneLadderOperatorAction
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax) := by
  have hdet' :
      inPlaneLadderDeterminant
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0 := by
    simpa [finiteCutoffContinuumBornDysonLadderDeterminant] using hdet
  simpa [finiteCutoffContinuumBornDysonLadderSolvedVertex,
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficient,
    finiteCutoffContinuumBornDysonLadderSolvedYCoefficient] using
    (inPlaneLadderSolvedVertex_fixedPoint
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
        v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
        v m probeEnergy broadening disorderStrength hbar pMax)
      hdet')

@[simp] theorem finiteCutoffContinuumBornDysonLadderDeterminant_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderDeterminant
      v m probeEnergy broadening 0 hbar pMax = 1 := by
  simp [finiteCutoffContinuumBornDysonLadderDeterminant, inPlaneLadderDeterminant]

@[simp] theorem finiteCutoffContinuumBornDysonLadderSolvedXCoefficient_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening 0 hbar pMax = 1 := by
  simp [finiteCutoffContinuumBornDysonLadderSolvedXCoefficient,
    inPlaneLadderSolvedXCoefficient, inPlaneLadderDeterminant]

@[simp] theorem finiteCutoffContinuumBornDysonLadderSolvedYCoefficient_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornDysonLadderSolvedYCoefficient]

@[simp] theorem finiteCutoffContinuumBornDysonLadderSolvedVertex_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedVertex
      v m probeEnergy broadening 0 hbar pMax = matrixOperator sigmaX := by
  simp [finiteCutoffContinuumBornDysonLadderSolvedVertex_eq]

end

end AnomalousHall.MassiveDirac
