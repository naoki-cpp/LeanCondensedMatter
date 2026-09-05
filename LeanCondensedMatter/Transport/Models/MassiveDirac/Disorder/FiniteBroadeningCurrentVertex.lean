import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.InPlaneLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current vertex

This module owns the finite-cutoff finite-external-broadening Born-Dyson current-vertex chain from
fixed-radius angular reduction through radial normalization to the solved in-plane ladder vertex.
The Cartesian propagator is reduced to the shared massive-Dirac polar Pauli algebra, producing the
repository-oriented in-plane action

```text
α σₓ + β σᵧ ↦ (X α - Y β) σₓ + (Y α + X β) σᵧ.
```

Radial integration then attaches the polar Jacobian `p dp`, one scalar-disorder line, and the
physical momentum measure `momentumMeasurePrefactor hbar` exactly once. The resulting normalized
coefficient pair is consumed by the canonical two-component ladder solution in `InPlaneLadder`.

This module does not insert the solved vertex into Kubo/Středa, take broadening or disorder limits,
or identify the Born-Dyson approximation with an exact disorder average.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-! ## Angular reduction -/

/-- The Cartesian finite-`η` Born-Dyson propagator reduces exactly to the shared polar Pauli form. -/
private theorem finiteCutoffContinuumBornDysonGreenOperator_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      polarPauliOperator
        (finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonXCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonZCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax) θ := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hradial :
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 = p ^ 2 + 0 ^ 2 := by
    calc
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = p ^ 2 := by rw [htrig]; ring
      _ = p ^ 2 + 0 ^ 2 := by ring
  have hden :
      finiteCutoffContinuumBornDysonDenominator
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    rw [hradial]
  simpa [finiteCutoffContinuumBornDysonGreenOperator,
    finiteCutoffContinuumBornDysonGreenMatrix,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonXCoefficient,
    finiteCutoffContinuumBornDysonYCoefficient,
    finiteCutoffContinuumBornDysonZCoefficient, hden] using
    (commonDenominatorPauliOperator_polar_eq
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax)
      v p θ)

/-- Full-angle `σₓ` coefficient of the finite-`η` Born-Dyson retarded-advanced rung. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  pauliRungAngularXCoefficient
    (finiteCutoffContinuumBornDysonScalarCoefficient
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonScalarCoefficient
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonZCoefficient
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonZCoefficient
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)

/-- Full-angle orientation-sensitive `σᵧ` coefficient of the finite-`η` Born-Dyson
retarded-advanced rung. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  pauliRungAngularYCoefficient
    (finiteCutoffContinuumBornDysonScalarCoefficient
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonScalarCoefficient
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonZCoefficient
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonZCoefficient
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)

/-- Full polar-angle finite-`η` Born-Dyson action on an arbitrary in-plane Pauli vertex. -/
noncomputable def finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax *
      matrixOperator (alpha • sigmaX + beta • sigmaY) *
      finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax

/-- The finite-`η` Born-Dyson full-angle rung acts on in-plane coefficients by the
repository-oriented rotation matrix `[[X,-Y],[Y,X]]`. -/
theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
        v m p probeEnergy broadening disorderStrength hbar pMax alpha beta =
      (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax * alpha -
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax * beta) •
          matrixOperator sigmaX +
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax * alpha +
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax * beta) •
          matrixOperator sigmaY := by
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonXCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonXCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonZCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonZCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  unfold finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
  have hpolar :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          matrixOperator (alpha • sigmaX + beta • sigmaY) *
          finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) =
        fun θ : ℝ =>
          polarPauliOperator aR bR dR θ *
            matrixOperator (alpha • sigmaX + beta • sigmaY) *
            polarPauliOperator aA bA dA θ := by
    funext θ
    rw [finiteCutoffContinuumBornDysonGreenOperator_polar_eq,
      finiteCutoffContinuumBornDysonGreenOperator_polar_eq]
  rw [hpolar]
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
    aR, aA, bR, bA, dR, dA] using
    (integral_polarPauliOperator_inPlane_eq aR aA bR bA dR dA alpha beta)

/-! ## Radial normalization -/

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

/-! ## Ladder specialization -/

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
