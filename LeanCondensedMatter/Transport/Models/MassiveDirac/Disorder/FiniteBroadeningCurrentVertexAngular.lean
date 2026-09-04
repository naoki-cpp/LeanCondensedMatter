import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current vertex

This module reduces the fixed-radius finite-external-broadening Born-Dyson retarded-advanced current
rung to the shared massive-Dirac polar Pauli algebra. The concrete propagator owns its Cartesian
coefficients and a proof-local polar reduction; the public result is the action on an arbitrary
in-plane Pauli vertex.

For repository orientation `Gᴿ Γ Gᴬ`,

```text
α σₓ + β σᵧ ↦ (X α - Y β) σₓ + (Y α + X β) σᵧ.
```

Radial momentum integration, disorder normalization, and the ladder fixed-point solve remain
downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

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
  have hmatrix :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix
          (finiteCutoffContinuumBornDysonScalarCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonZCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) θ := by
    unfold finiteCutoffContinuumBornDysonGreenMatrix polarPauliMatrix
    unfold finiteCutoffContinuumBornDysonScalarCoefficient
      finiteCutoffContinuumBornDysonXCoefficient
      finiteCutoffContinuumBornDysonYCoefficient
      finiteCutoffContinuumBornDysonZCoefficient
      finiteCutoffContinuumBornDysonDenominator
    rw [hradial]
    push_cast
    ring_nf
  simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator] using
    congrArg matrixOperator hmatrix

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

end

end AnomalousHall.MassiveDirac
