import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current-vertex angular reduction

This module performs the finite-external-broadening current-rung reduction using the actual
Born-Dyson propagator from `FiniteBroadeningBornPropagator.lean`.  Rotational invariance of the Born
self-energy leaves the propagator in the polar Pauli form

```text
G_B,s(p,θ) = a_s(p) I + b_s(p) cosθ σₓ + b_s(p) sinθ σᵧ + d_s(p) σ_z.
```

The pointwise retarded-advanced products with `σₓ` and `σᵧ` are then kept explicitly oriented for
the later full-angle reduction.  The radial coefficients remain the existing finite-cutoff
finite-`η` Born-Dyson coefficients; no parallel propagator or self-energy API is introduced.
Radial integration, disorder normalization, ladder resummation, and broadening/disorder limits
remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

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

/-- Operator form of the exact polar Pauli decomposition. -/
theorem finiteCutoffContinuumBornDysonGreenOperator_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        (((Real.cos θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) •
          matrixOperator sigmaX +
        (((Real.sin θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) •
          matrixOperator sigmaY +
        finiteCutoffContinuumBornDysonZCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax •
          matrixOperator sigmaZ := by
  unfold finiteCutoffContinuumBornDysonGreenOperator
  rw [finiteCutoffContinuumBornDysonGreenMatrix_polar_eq]
  simp [matrixOperator, map_add, map_smul]

private def bornDysonRaPauliXScalarCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  ((Real.cos θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (bA * dR - bR * dA)

private def bornDysonRaPauliXXCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  aR * aA - dR * dA +
    bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

private def bornDysonRaPauliXYCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  Complex.I * (aA * dR - aR * dA) +
    2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)

private def bornDysonRaPauliXZCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  ((Real.cos θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (aR * bA - aA * bR)

/-- Exact pointwise Pauli decomposition of the finite-`η` Born-Dyson `Gᴿ σₓ Gᴬ` product. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedPauliX_polar_eq
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenMatrix
        .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax * sigmaX *
      finiteCutoffContinuumBornDysonGreenMatrix
        .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      bornDysonRaPauliXScalarCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
        bornDysonRaPauliXXCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • sigmaX +
        bornDysonRaPauliXYCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • sigmaY +
        bornDysonRaPauliXZCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • sigmaZ := by
  rw [finiteCutoffContinuumBornDysonGreenMatrix_polar_eq,
    finiteCutoffContinuumBornDysonGreenMatrix_polar_eq]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bornDysonRaPauliXScalarCoefficient, bornDysonRaPauliXXCoefficient,
      bornDysonRaPauliXYCoefficient, bornDysonRaPauliXZCoefficient,
      Matrix.mul_apply, sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

private def bornDysonRaPauliYScalarCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  ((Real.sin θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
    Complex.I * ((Real.cos θ : ℝ) : ℂ) * (bR * dA - bA * dR)

private def bornDysonRaPauliYXCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  -Complex.I * (aA * dR - aR * dA) +
    2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)

private def bornDysonRaPauliYYCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  aR * aA - dR * dA -
    bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

private def bornDysonRaPauliYZCoefficient
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
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
  ((Real.sin θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
    Complex.I * ((Real.cos θ : ℝ) : ℂ) * (aA * bR - aR * bA)

/-- Exact pointwise Pauli decomposition of the finite-`η` Born-Dyson `Gᴿ σᵧ Gᴬ` product. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedPauliY_polar_eq
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenMatrix
        .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax * sigmaY *
      finiteCutoffContinuumBornDysonGreenMatrix
        .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      bornDysonRaPauliYScalarCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
        bornDysonRaPauliYXCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • sigmaX +
        bornDysonRaPauliYYCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • sigmaY +
        bornDysonRaPauliYZCoefficient
          v m p θ probeEnergy broadening disorderStrength hbar pMax • sigmaZ := by
  rw [finiteCutoffContinuumBornDysonGreenMatrix_polar_eq,
    finiteCutoffContinuumBornDysonGreenMatrix_polar_eq]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bornDysonRaPauliYScalarCoefficient, bornDysonRaPauliYXCoefficient,
      bornDysonRaPauliYYCoefficient, bornDysonRaPauliYZCoefficient,
      Matrix.mul_apply, sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

/-- Full-angle `σₓ` coefficient expected from the finite-`η` Born-Dyson retarded-advanced rung. -/
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

/-- Full-angle orientation-sensitive `σᵧ` coefficient expected from the finite-`η` Born-Dyson
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

end

end AnomalousHall.MassiveDirac
