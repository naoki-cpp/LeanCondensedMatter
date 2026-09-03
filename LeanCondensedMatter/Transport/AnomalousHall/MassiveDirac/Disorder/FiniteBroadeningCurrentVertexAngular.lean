import LeanCondensedMatter.Transport.Models.MassiveDirac.AngularReduction
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.CurrentVertexAngular
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current vertex

This module derives the fixed-radius retarded-advanced current rung from the finite-cutoff,
finite-external-broadening Born-Dyson propagator.  The derivation is performed once for an arbitrary
in-plane Pauli vertex `α σₓ + β σᵧ`; the `σₓ` and `σᵧ` basis rungs are corollaries.

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

private def bornDysonRaInPlaneScalarCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) : ℂ :=
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
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let common := aA * bR + aR * bA
  let skew := bA * dR - bR * dA
  alpha * (c * common + Complex.I * s * skew) +
    beta * (s * common - Complex.I * c * skew)

private def bornDysonRaInPlaneXCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) : ℂ :=
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
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let core := aR * aA - dR * dA
  let delta := aA * dR - aR * dA
  let quad := bR * bA * (c ^ 2 - s ^ 2)
  let mix := 2 * bR * bA * c * s
  alpha * (core + quad) + beta * ((-Complex.I) * delta + mix)

private def bornDysonRaInPlaneYCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) : ℂ :=
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
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let core := aR * aA - dR * dA
  let delta := aA * dR - aR * dA
  let quad := bR * bA * (c ^ 2 - s ^ 2)
  let mix := 2 * bR * bA * c * s
  alpha * (Complex.I * delta + mix) + beta * (core - quad)

private def bornDysonRaInPlaneZCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) : ℂ :=
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
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let sum := bA * dR + bR * dA
  let skew := aR * bA - aA * bR
  alpha * (c * sum + Complex.I * s * skew) +
    beta * (s * sum - Complex.I * c * skew)

/-- Exact pointwise Pauli decomposition of
`Gᴿ_B (α σₓ + β σᵧ) Gᴬ_B` at fixed polar momentum. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedInPlane_polar_eq
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) :
    finiteCutoffContinuumBornDysonGreenMatrix
        .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax *
      (alpha • sigmaX + beta • sigmaY) *
      finiteCutoffContinuumBornDysonGreenMatrix
        .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      bornDysonRaInPlaneScalarCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta • (1 : Matrix2) +
        bornDysonRaInPlaneXCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta • sigmaX +
        bornDysonRaInPlaneYCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta • sigmaY +
        bornDysonRaInPlaneZCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta • sigmaZ := by
  rw [finiteCutoffContinuumBornDysonGreenMatrix_polar_eq,
    finiteCutoffContinuumBornDysonGreenMatrix_polar_eq]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bornDysonRaInPlaneScalarCoefficient, bornDysonRaInPlaneXCoefficient,
      bornDysonRaInPlaneYCoefficient, bornDysonRaInPlaneZCoefficient,
      Matrix.mul_apply, sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

/-- Full-angle `σₓ` coefficient of the finite-`η` Born-Dyson retarded-advanced rung. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornDysonZCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonZCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)

/-- Full-angle orientation-sensitive `σᵧ` coefficient of the finite-`η` Born-Dyson
retarded-advanced rung. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) * Complex.I *
    (finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonZCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonZCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)

private theorem integral_finiteBorn_cos_sin_linear_zero (cCos cSin : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℝ) : ℂ) * cCos + ((Real.sin θ : ℝ) : ℂ) * cSin) = 0 := by
  have hcos : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_complex_cos_zero_two_pi,
    integral_complex_sin_zero_two_pi]
  simp

private theorem integral_finiteBorn_inPlane_modes (c0 c2 cMix : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      c0 +
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2 +
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * cMix) =
      (((2 * Real.pi : ℝ) : ℂ)) * c0 := by
  have hconst : IntervalIntegrable (fun _θ : ℝ => c0) volume 0 (2 * Real.pi) := by
    exact continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hquad : IntervalIntegrable
      (fun θ : ℝ =>
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmix : IntervalIntegrable
      (fun θ : ℝ =>
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * cMix)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add (hconst.add hquad) hmix,
    intervalIntegral.integral_add hconst hquad,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_complex_cos_sq_sub_sin_sq_zero_two_pi,
    integral_complex_cos_mul_sin_zero_two_pi]
  simp

private theorem integral_finiteBorn_pauli_decomposition
    (scalarCoefficient xCoefficient yCoefficient zCoefficient : ℝ → ℂ)
    (hscalarContinuous : Continuous scalarCoefficient)
    (hxContinuous : Continuous xCoefficient)
    (hyContinuous : Continuous yCoefficient)
    (hzContinuous : Continuous zCoefficient)
    (scalarIntegral xIntegral yIntegral zIntegral : ℂ)
    (hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = scalarIntegral)
    (hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) = xIntegral)
    (hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) = yIntegral)
    (hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = zIntegral) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      scalarCoefficient θ • (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        xCoefficient θ • matrixOperator sigmaX +
        yCoefficient θ • matrixOperator sigmaY +
        zCoefficient θ • matrixOperator sigmaZ) =
      scalarIntegral • (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        xIntegral • matrixOperator sigmaX +
        yIntegral • matrixOperator sigmaY +
        zIntegral • matrixOperator sigmaZ := by
  have hscalar : IntervalIntegrable
      (fun θ : ℝ => scalarCoefficient θ • (1 : DiracHilbert →L[ℂ] DiracHilbert))
      volume 0 (2 * Real.pi) := by
    exact (hscalarContinuous.smul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hx : IntervalIntegrable
      (fun θ : ℝ => xCoefficient θ • matrixOperator sigmaX) volume 0 (2 * Real.pi) := by
    exact (hxContinuous.smul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hy : IntervalIntegrable
      (fun θ : ℝ => yCoefficient θ • matrixOperator sigmaY) volume 0 (2 * Real.pi) := by
    exact (hyContinuous.smul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hz : IntervalIntegrable
      (fun θ : ℝ => zCoefficient θ • matrixOperator sigmaZ) volume 0 (2 * Real.pi) := by
    exact (hzContinuous.smul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_add ((hscalar.add hx).add hy) hz,
    intervalIntegral.integral_add (hscalar.add hx) hy,
    intervalIntegral.integral_add hscalar hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [hScalarIntegral, hXIntegral, hYIntegral, hZIntegral]

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
  let aR : ℂ := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aA : ℂ := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR : ℂ := finiteCutoffContinuumBornDysonXCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA : ℂ := finiteCutoffContinuumBornDysonXCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR : ℂ := finiteCutoffContinuumBornDysonZCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA : ℂ := finiteCutoffContinuumBornDysonZCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let scalarCoefficient : ℝ → ℂ := fun θ =>
    bornDysonRaInPlaneScalarCoefficient
      v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta
  let xCoefficient : ℝ → ℂ := fun θ =>
    bornDysonRaInPlaneXCoefficient
      v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta
  let yCoefficient : ℝ → ℂ := fun θ =>
    bornDysonRaInPlaneYCoefficient
      v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta
  let zCoefficient : ℝ → ℂ := fun θ =>
    bornDysonRaInPlaneZCoefficient
      v m p θ probeEnergy broadening disorderStrength hbar pMax alpha beta
  have hpointwise :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          matrixOperator (alpha • sigmaX + beta • sigmaY) *
          finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) =
      fun θ : ℝ =>
        scalarCoefficient θ • (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          xCoefficient θ • matrixOperator sigmaX +
          yCoefficient θ • matrixOperator sigmaY +
          zCoefficient θ • matrixOperator sigmaZ := by
    funext θ
    unfold finiteCutoffContinuumBornDysonGreenOperator
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
            probeEnergy broadening disorderStrength hbar pMax) = _
    rw [← map_mul, ← map_mul,
      finiteCutoffContinuumBornDysonRetardedAdvancedInPlane_polar_eq]
    simp [scalarCoefficient, xCoefficient, yCoefficient, zCoefficient,
      matrixOperator, map_add, map_smul]
  have hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = 0 := by
    convert integral_finiteBorn_cos_sin_linear_zero
      (alpha * (aA * bR + aR * bA) -
        beta * Complex.I * (bA * dR - bR * dA))
      (alpha * Complex.I * (bA * dR - bR * dA) +
        beta * (aA * bR + aR * bA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [scalarCoefficient, bornDysonRaInPlaneScalarCoefficient,
      aR, aA, bR, bA, dR, dA]
    ring
  have hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) =
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax * alpha -
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax * beta := by
    convert integral_finiteBorn_inPlane_modes
      ((aR * aA - dR * dA) * alpha -
        Complex.I * (aA * dR - aR * dA) * beta)
      (bR * bA * alpha)
      (2 * bR * bA * beta) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [xCoefficient, bornDysonRaInPlaneXCoefficient,
        aR, aA, bR, bA, dR, dA]
      ring
    · simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
        aR, aA, dR, dA]
      ring
  have hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) =
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax * alpha +
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
            v m p probeEnergy broadening disorderStrength hbar pMax * beta := by
    convert integral_finiteBorn_inPlane_modes
      (Complex.I * (aA * dR - aR * dA) * alpha +
        (aR * aA - dR * dA) * beta)
      (-(bR * bA * beta))
      (2 * bR * bA * alpha) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [yCoefficient, bornDysonRaInPlaneYCoefficient,
        aR, aA, bR, bA, dR, dA]
      ring
    · simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
        aR, aA, dR, dA]
      ring
  have hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = 0 := by
    convert integral_finiteBorn_cos_sin_linear_zero
      (alpha * (bA * dR + bR * dA) -
        beta * Complex.I * (aR * bA - aA * bR))
      (alpha * Complex.I * (aR * bA - aA * bR) +
        beta * (bA * dR + bR * dA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [zCoefficient, bornDysonRaInPlaneZCoefficient,
      aR, aA, bR, bA, dR, dA]
    ring
  have hscalarContinuous : Continuous scalarCoefficient := by
    dsimp [scalarCoefficient, bornDysonRaInPlaneScalarCoefficient]
    fun_prop
  have hxContinuous : Continuous xCoefficient := by
    dsimp [xCoefficient, bornDysonRaInPlaneXCoefficient]
    fun_prop
  have hyContinuous : Continuous yCoefficient := by
    dsimp [yCoefficient, bornDysonRaInPlaneYCoefficient]
    fun_prop
  have hzContinuous : Continuous zCoefficient := by
    dsimp [zCoefficient, bornDysonRaInPlaneZCoefficient]
    fun_prop
  unfold finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
  rw [hpointwise]
  rw [integral_finiteBorn_pauli_decomposition
    scalarCoefficient xCoefficient yCoefficient zCoefficient
    hscalarContinuous hxContinuous hyContinuous hzContinuous
    0
    (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
        v m p probeEnergy broadening disorderStrength hbar pMax * alpha -
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
        v m p probeEnergy broadening disorderStrength hbar pMax * beta)
    (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
        v m p probeEnergy broadening disorderStrength hbar pMax * alpha +
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
        v m p probeEnergy broadening disorderStrength hbar pMax * beta)
    0 hScalarIntegral hXIntegral hYIntegral hZIntegral]
  simp

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