import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagatorPolar
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.InPlaneLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current vertex

This module owns the finite-cutoff finite-external-broadening Born-Dyson current-vertex chain from
fixed-radius angular reduction through radial normalization to the algebraic in-plane ladder
coefficients. The Cartesian-to-polar Born-Dyson propagator bridge is shared upstream by
`FiniteBroadeningBornPropagatorPolar`; this module consumes that representation to obtain the
repository-oriented in-plane action

```text
K = [[X,-Y],[Y,X]].
```

Angular and radial rung coefficients are indexed by their output/input directions. Coordinate-
specific consumers specialize those indices, while the ladder uses the canonical entries `Kxx`
and `Kyx`. Radial integration attaches the polar Jacobian `p dp`, one scalar-disorder line, and the
physical momentum measure `momentumMeasurePrefactor hbar` exactly once. Their interpretation as the
actual fixed point requires the shared determinant condition owned by `FiniteBroadeningLadderRegularity`.

This module does not insert the vertex into Kubo/Středa, take broadening or disorder limits, or
identify the Born-Dyson approximation with an exact disorder average.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-! ## Angular reduction -/

/-- Entry `(i,j)` of the full-angle finite-`η` Born-Dyson retarded-advanced in-plane rung. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
    (i j : Direction2)
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneRotationCoefficient
    (pauliRungAngularXCoefficient
      (finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax))
    (pauliRungAngularYCoefficient
      (finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax))
    i j

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

/-- The finite-`η` Born-Dyson full-angle rung acts by its direction-indexed in-plane matrix. -/
theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
        v m p probeEnergy broadening disorderStrength hbar pMax alpha beta =
      (finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          .x .x v m p probeEnergy broadening disorderStrength hbar pMax * alpha +
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          .x .y v m p probeEnergy broadening disorderStrength hbar pMax * beta) •
          matrixOperator sigmaX +
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
            .y .x v m p probeEnergy broadening disorderStrength hbar pMax * alpha +
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
            .y .y v m p probeEnergy broadening disorderStrength hbar pMax * beta) •
          matrixOperator sigmaY := by
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonPauliCoefficient .z
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
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient,
    inPlaneRotationCoefficient, aR, aA, bR, bA, dR, dA, sub_eq_add_neg] using
    (integral_polarPauliOperator_inPlane_eq aR aA bR bA dR dA alpha beta)

/-! ## Radial normalization -/

/-- Normalized finite-`η` radial current-rung entry `(i,j)`. The angular `2π` is already included
upstream, so the normalization attaches the scalar-disorder line and `d²p/(2πℏ)²` prefactor once. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
    (i j : Direction2)
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
      i j v m p probeEnergy broadening disorderStrength hbar pMax

/-- Normalized finite-cutoff finite-`η` current-rung entry `(i,j)` supplied downstream. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    (i j : Direction2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
      i j v m p probeEnergy broadening disorderStrength hbar pMax

@[simp] theorem finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_zero_disorder
    (i j : Direction2) (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
      i j v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand]

/-! ## Ladder specialization -/

/-- Output component of the normalized finite-`η` Born-Dyson ladder fixed point for a bare
`σₓ` source. The interpretation as the actual fixed-point coefficient requires
`finiteCutoffContinuumBornDysonLadderRegular`. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    (output : Direction2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let x := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    .x .x v m probeEnergy broadening disorderStrength hbar pMax
  let y := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    .y .x v m probeEnergy broadening disorderStrength hbar pMax
  inPlaneRotationCoefficient
    (inPlaneLadderSolvedXCoefficient x y)
    (inPlaneLadderSolvedYCoefficient x y)
    output .x

@[simp] theorem finiteCutoffContinuumBornDysonLadderSolvedCoefficient_zero_disorder
    (output : Direction2) (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedCoefficient
      output v m probeEnergy broadening 0 hbar pMax =
      inPlaneRotationCoefficient 1 0 output .x := by
  cases output <;>
    simp [finiteCutoffContinuumBornDysonLadderSolvedCoefficient,
      inPlaneRotationCoefficient, inPlaneLadderSolvedXCoefficient,
      inPlaneLadderSolvedYCoefficient, inPlaneLadderDeterminant]

end

end QuantumTheory.Transport.Models.MassiveDirac
