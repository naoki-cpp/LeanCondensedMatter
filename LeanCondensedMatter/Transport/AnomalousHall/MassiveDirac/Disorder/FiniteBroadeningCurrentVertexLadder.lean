import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.InPlaneLadder

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson ladder specialization

This module specializes the canonical two-component in-plane ladder solution to the normalized
finite-cutoff finite-external-broadening Born-Dyson rung coefficients. The fixed-point algebra and
its determinant remain owned by `InPlaneLadder.lean`; this file only names the solved coefficient
pair and the longitudinal/transverse bounded vertices consumed downstream.

For repository orientation `Gᴿ Γ Gᴬ`, the bare-`σᵧ` solution is the canonical rotation `(-β, α)` of
the bare-`σₓ` solved pair `(α, β)`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

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

/-- Bounded dimensionless in-plane current vertex for a bare `σₓ` source. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedVertex
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneLadderSolvedVertex
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- Bounded dimensionless in-plane current vertex for a bare `σᵧ` source, obtained by rotating the
canonical bare-`σₓ` solved pair. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  (-finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax) • matrixOperator sigmaX +
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaY

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
