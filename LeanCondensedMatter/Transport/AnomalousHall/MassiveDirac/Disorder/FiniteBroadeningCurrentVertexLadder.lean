import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.InPlaneLadder

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson ladder specialization

This module specializes the canonical two-component in-plane ladder solution to the normalized
finite-cutoff finite-external-broadening Born-Dyson rung coefficients.  It introduces no second
fixed-point algebra: the determinant, solved coefficients, and bounded solved vertex are direct
specializations of `InPlaneLadder.lean`.

The repository orientation remains `Gᴿ Γ Gᴬ`, so the transverse coefficient has the same sign as the
normalized radial `Y` coefficient.  The bare-`σᵧ` source needed by the Hall channel is obtained only
by rotating the solved bare-`σₓ` pair from `(α, β)` to `(-β, α)`.  Physical charge-current conversion
and Kubo/Středa insertion remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

private theorem inPlaneLadderRotatedSolvedVertex_fixedPoint
    (x y : ℂ) (hdet : inPlaneLadderDeterminant x y ≠ 0) :
    (-inPlaneLadderSolvedYCoefficient x y) • matrixOperator sigmaX +
        inPlaneLadderSolvedXCoefficient x y • matrixOperator sigmaY =
      matrixOperator sigmaY +
        inPlaneLadderOperatorAction x y
          (-inPlaneLadderSolvedYCoefficient x y)
          (inPlaneLadderSolvedXCoefficient x y) := by
  have hX := inPlaneLadderSolvedXCoefficient_fixedPoint x y hdet
  have hY := inPlaneLadderSolvedYCoefficient_fixedPoint x y hdet
  unfold inPlaneLadderXCoefficient at hX
  unfold inPlaneLadderYCoefficient at hY
  have hrotX :
      x * (-inPlaneLadderSolvedYCoefficient x y) -
          y * inPlaneLadderSolvedXCoefficient x y =
        -inPlaneLadderSolvedYCoefficient x y := by
    linear_combination hY
  have hrotY :
      y * (-inPlaneLadderSolvedYCoefficient x y) +
          x * inPlaneLadderSolvedXCoefficient x y =
        inPlaneLadderSolvedXCoefficient x y - 1 := by
    linear_combination hX
  unfold inPlaneLadderOperatorAction inPlaneLadderXCoefficient inPlaneLadderYCoefficient
  rw [hrotX, hrotY]
  module

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
Born-Dyson ladder for a bare `σₓ` source. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedVertex
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedVertex
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

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

/-- Bounded dimensionless current vertex solving the same ladder for a bare `σᵧ` source.  Rotational
closure fixes it to the canonical rotation `(-β, α)` of the solved bare-`σₓ` pair. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  (-finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax) • matrixOperator sigmaX +
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaY

/-- The rotated finite-`η` Born-Dyson vertex solves `Γᵧ = σᵧ + L(Γᵧ)` under the same determinant
hypothesis as the longitudinal solution. -/
theorem finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex_fixedPoint
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminant
      v m probeEnergy broadening disorderStrength hbar pMax ≠ 0) :
    finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex
        v m probeEnergy broadening disorderStrength hbar pMax =
      matrixOperator sigmaY +
        inPlaneLadderOperatorAction
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (-finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax) := by
  have hdet' :
      inPlaneLadderDeterminant
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
            v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0 := by
    simpa [finiteCutoffContinuumBornDysonLadderDeterminant] using hdet
  simpa [finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex,
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficient,
    finiteCutoffContinuumBornDysonLadderSolvedYCoefficient] using
    (inPlaneLadderRotatedSolvedVertex_fixedPoint
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
  simp [finiteCutoffContinuumBornDysonLadderSolvedVertex,
    inPlaneLadderSolvedVertex, inPlaneLadderSolvedXCoefficient,
    inPlaneLadderSolvedYCoefficient, inPlaneLadderDeterminant]

@[simp] theorem finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex
      v m probeEnergy broadening 0 hbar pMax = matrixOperator sigmaY := by
  simp [finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex]

end

end AnomalousHall.MassiveDirac
