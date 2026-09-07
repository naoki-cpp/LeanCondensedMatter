import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
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
physical momentum measure `momentumMeasurePrefactor hbar` exactly once. This module also owns the
common RA denominator form and the determinant condition that licenses interpreting the algebraic
coefficient pair as the actual ladder fixed point.

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

/-! ## Common denominator form -/

/-- Numerator of entry `(i,j)` of the finite-`η` Born-Dyson in-plane rung before the common RA
denominator is attached. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
    (i j : Direction2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneRotationCoefficient
    (finiteCutoffContinuumBornEffectiveEnergy
        .retarded v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveEnergy
        .advanced v m probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornEffectiveMass
        .retarded v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMass
        .advanced v m probeEnergy broadening disorderStrength hbar pMax)
    (Complex.I *
      (finiteCutoffContinuumBornEffectiveEnergy
          .advanced v m probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornEffectiveMass
          .retarded v m probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornEffectiveEnergy
          .retarded v m probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornEffectiveMass
          .advanced v m probeEnergy broadening disorderStrength hbar pMax))
    i j

/-- The common finite-`η` RA denominator product is nonzero whenever the Born-Dyson invertibility
hypotheses hold. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_ne_zero
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
      v m p probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
  exact mul_ne_zero
    (finiteCutoffContinuumBornDysonDenominator_ne_zero
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax)
    (finiteCutoffContinuumBornDysonDenominator_ne_zero
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax)

/-- Closed common-denominator form of every entry `(i,j)` of the full-angle finite-`η` Born-Dyson
retarded-advanced rung. Coordinate-specific consumers specialize `i` and `j`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm
    (i j : Direction2)
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
        i j v m p probeEnergy broadening disorderStrength hbar pMax =
      (((2 * Real.pi : ℝ) : ℂ)) *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
          i j v m probeEnergy broadening disorderStrength hbar pMax := by
  cases i <;> cases j <;>
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient,
      inPlaneRotationCoefficient,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      pauliRungAngularXCoefficient, pauliRungAngularYCoefficient,
      finiteCutoffContinuumBornDysonScalarCoefficient,
      finiteCutoffContinuumBornDysonPauliCoefficient, pauliAxisComponent,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct,
      mul_inv_rev] <;>
    ring

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

/-- Regularity condition under which the finite-cutoff Born-Dyson in-plane ladder coefficient pair
represents the actual fixed-point solution. -/
def finiteCutoffContinuumBornDysonLadderRegular
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : Prop :=
  inPlaneLadderDeterminant
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
        .x .x v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
        .y .x v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0

/-- At zero disorder the finite-cutoff Born-Dyson ladder determinant is one. -/
@[simp]
theorem finiteCutoffContinuumBornDysonLadderRegular_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening 0 hbar pMax := by
  simp [finiteCutoffContinuumBornDysonLadderRegular, inPlaneLadderDeterminant]

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
  inPlaneLadderSolvedCoefficient output x y

@[simp] theorem finiteCutoffContinuumBornDysonLadderSolvedCoefficient_zero_disorder
    (output : Direction2) (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderSolvedCoefficient
      output v m probeEnergy broadening 0 hbar pMax =
      inPlaneRotationCoefficient 1 0 output .x := by
  cases output <;>
    simp [finiteCutoffContinuumBornDysonLadderSolvedCoefficient,
      inPlaneLadderSolvedCoefficient, inPlaneRotationCoefficient,
      inPlaneLadderSolvedXCoefficient, inPlaneLadderSolvedYCoefficient,
      inPlaneLadderDeterminant]

end

end QuantumTheory.Transport.Models.MassiveDirac
