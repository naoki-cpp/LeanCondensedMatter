import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.CurrentVertexAngular
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.PauliRung
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current vertex

This module derives the fixed-radius retarded-advanced current rung from the finite-cutoff,
finite-external-broadening Born-Dyson propagator. The propagator-specific polar reduction supplies
the six radial Pauli coefficients to the shared massive-Dirac rung algebra, which handles an
arbitrary in-plane Pauli vertex `α σₓ + β σᵧ`; the `σₓ` and `σᵧ` basis rungs are corollaries.

For repository orientation `Gᴿ Γ Gᴬ`, the full-angle action is

```text
α σₓ + β σᵧ ↦ (X α - Y β) σₓ + (Y α + X β) σᵧ.
```

Radial momentum integration, the scalar-disorder line, momentum-measure normalization, and ladder
fixed-point solve remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- The finite-`η` Born-Dyson denominator is rotationally invariant in the momentum plane. -/
theorem finiteCutoffContinuumBornDysonDenominator_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDenominator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hrad :
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 = p ^ 2 := by
    calc
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = p ^ 2 := by rw [htrig]; ring
  simp [finiteCutoffContinuumBornDysonDenominator, hrad]

/-- The scalar Born-Dyson Pauli coefficient is independent of polar angle. -/
theorem finiteCutoffContinuumBornDysonScalarCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonScalarCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonScalarCoefficient
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonScalarCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]

/-- The `σₓ` Born-Dyson coefficient is the radial in-plane coefficient times `cos θ`. -/
theorem finiteCutoffContinuumBornDysonXCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonXCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      ((Real.cos θ : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonXCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonXCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]
  push_cast
  ring

/-- The `σᵧ` Born-Dyson coefficient is the same radial in-plane coefficient times `sin θ`. -/
theorem finiteCutoffContinuumBornDysonYCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonYCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      ((Real.sin θ : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonXCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonYCoefficient finiteCutoffContinuumBornDysonXCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]
  push_cast
  ring

/-- The `σ_z` Born-Dyson Pauli coefficient is independent of polar angle. -/
theorem finiteCutoffContinuumBornDysonZCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonZCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonZCoefficient
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonZCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]

/-- Exact polar Pauli form of the finite-`η` Born-Dyson Green matrix. -/
theorem finiteCutoffContinuumBornDysonGreenMatrix_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenMatrix
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
        (((Real.cos θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) • sigmaX +
        (((Real.sin θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) • sigmaY +
        finiteCutoffContinuumBornDysonZCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax • sigmaZ := by
  unfold finiteCutoffContinuumBornDysonGreenMatrix
  rw [finiteCutoffContinuumBornDysonScalarCoefficient_polar,
    finiteCutoffContinuumBornDysonXCoefficient_polar,
    finiteCutoffContinuumBornDysonYCoefficient_polar,
    finiteCutoffContinuumBornDysonZCoefficient_polar]

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
  rw [show
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
            polarPauliOperator aA bA dA θ by
    funext θ
    unfold finiteCutoffContinuumBornDysonGreenOperator polarPauliOperator
    change
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (finiteCutoffContinuumBornDysonGreenMatrix
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (alpha • sigmaX + beta • sigmaY) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (finiteCutoffContinuumBornDysonGreenMatrix
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) =
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aR bR dR θ) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (alpha • sigmaX + beta • sigmaY) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aA bA dA θ)
    rw [finiteCutoffContinuumBornDysonGreenMatrix_polar_eq,
      finiteCutoffContinuumBornDysonGreenMatrix_polar_eq]
    simp [polarPauliMatrix, aR, aA, bR, bA, dR, dA] ]
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
    aR, aA, bR, bA, dR, dA] using
    (integral_polarPauliOperator_inPlane_eq aR aA bR bA dR dA alpha beta)

/-- Full polar-angle `Gᴿ_B σₓ Gᴬ_B` rung, defined as the first basis case of the generic in-plane
action. -/
noncomputable def finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
    v m p probeEnergy broadening disorderStrength hbar pMax 1 0

/-- Full polar-angle `Gᴿ_B σᵧ Gᴬ_B` rung, defined as the second basis case of the generic in-plane
action. -/
noncomputable def finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
    v m p probeEnergy broadening disorderStrength hbar pMax 0 1

/-- The `σₓ` basis rung closes in the in-plane Pauli span. -/
theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaX +
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaY := by
  simpa [finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral] using
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_eq
      v m p probeEnergy broadening disorderStrength hbar pMax 1 0

/-- The `σᵧ` basis rung closes with the orientation-sensitive rotation
`σᵧ ↦ -Y σₓ + X σᵧ`. -/
theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
        v m p probeEnergy broadening disorderStrength hbar pMax =
      (-finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax) • matrixOperator sigmaX +
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaY := by
  simpa [finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral] using
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_eq
      v m p probeEnergy broadening disorderStrength hbar pMax 0 1

/-- At zero disorder strength, the finite-`η` Born-Dyson `σₓ` rung reduces exactly to the existing
clean finite-broadening angular rung. -/
@[simp] theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral_zero_disorder
    (v m p probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening 0 hbar pMax =
      continuumAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening := by
  simp [finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral,
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction,
    continuumAngularRetardedAdvancedPauliXIntegral]

end

end AnomalousHall.MassiveDirac
