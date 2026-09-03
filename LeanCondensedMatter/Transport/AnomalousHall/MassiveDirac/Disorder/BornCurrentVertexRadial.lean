import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Born-dressed radial retarded-advanced current rung

This Phase 5 bridge feeds the scalar and `σ_z` Born damping channels from `BornPropagator` into the
repository-oriented Green-product part of the current rung

```text
Gᴿ(p,θ) σₓ Gᴬ(p,θ).
```

The full polar-angle integral closes in the `σₓ`/`σᵧ` span. Its common retarded-advanced
denominator product is reduced to a manifestly real sum of squares, leaving one-dimensional radial
integrands ready for the next Lorentzian/arctangent evaluation.

The operator order is intentionally `Gᴿ σₓ Gᴬ`, matching `Transport.Disorder.Ladder`. Reversing the
retarded/advanced order reverses the orientation-sensitive `σᵧ` coefficient.

There are two normalization levels in this file and they are kept distinct:

* `...RadialXIntegrand` / `...RadialYIntegrand` contain the angular-integrated Green product and the
  polar Jacobian `p dp` only;
* `...CurrentRungRadialXIntegrand` / `...CurrentRungRadialYIntegrand` additionally attach the
  external scalar-disorder line and the physical momentum measure
  `disorderStrength * momentumMeasurePrefactor hbar`.

The angular coefficients already contain the full `2π` polar-angle factor. Therefore the full
current-rung normalization must use `momentumMeasurePrefactor hbar` directly, not
`continuumBornAngularMeasurePrefactor hbar`, which would count that `2π` a second time.

No radial integral, weak-disorder limit, ladder resummation, transport-lifetime identification,
Ward claim, or conductivity theorem is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Proof-only matrix adapter for the Born-dressed Pauli coefficients. -/
private def continuumBornPauliGreenMatrix
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : Matrix2 :=
  continuumBornPauliGreenScalarCoefficient
      side v m px py probeEnergy disorderStrength hbar • (1 : Matrix2) +
    continuumBornPauliGreenXCoefficient
      side v m px py probeEnergy disorderStrength hbar • sigmaX +
    continuumBornPauliGreenYCoefficient
      side v m px py probeEnergy disorderStrength hbar • sigmaY +
    continuumBornPauliGreenZCoefficient
      side v m px py probeEnergy disorderStrength hbar • sigmaZ

/-- Proof-only bounded-operator adapter of the Born-dressed Pauli matrix. -/
private def continuumBornPauliGreenOperator
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator
    (continuumBornPauliGreenMatrix
      side v m px py probeEnergy disorderStrength hbar)

/-- The Born-dressed denominator is radial in polar momentum coordinates. -/
@[simp] theorem continuumBornPauliGreenDenominator_polar
    (side : SpectralSide)
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenDenominator side v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      continuumBornPauliGreenDenominator
        side v m p 0 probeEnergy disorderStrength hbar := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq θ
  have hradial :
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 = p ^ 2 + 0 ^ 2 := by
    calc
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = p ^ 2 := by rw [htrig]; ring
      _ = p ^ 2 + 0 ^ 2 := by ring
  unfold continuumBornPauliGreenDenominator
  rw [hradial]

/-- The Born scalar coefficient is independent of the polar angle. -/
@[simp] theorem continuumBornPauliGreenScalarCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenScalarCoefficient side v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      continuumBornPauliGreenScalarCoefficient
        side v m p 0 probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenScalarCoefficient]

/-- The Born `σ_z` coefficient is independent of the polar angle. -/
@[simp] theorem continuumBornPauliGreenZCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenZCoefficient side v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      continuumBornPauliGreenZCoefficient
        side v m p 0 probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenZCoefficient]

/-- The Born `σₓ` coefficient carries the polar factor `cos θ`. -/
theorem continuumBornPauliGreenXCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenXCoefficient side v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      ((Real.cos θ : ℝ) : ℂ) *
        continuumBornPauliGreenXCoefficient
          side v m p 0 probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenXCoefficient]
  ring

/-- The Born `σᵧ` coefficient carries `sin θ` with the same radial amplitude as the `σₓ`
coefficient. -/
theorem continuumBornPauliGreenYCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenYCoefficient side v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      ((Real.sin θ : ℝ) : ℂ) *
        continuumBornPauliGreenXCoefficient
          side v m p 0 probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenYCoefficient, continuumBornPauliGreenXCoefficient]
  ring

private def bornRaPauliXScalarCoefficient
    (v m p θ probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  let aR := continuumBornPauliGreenScalarCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let aA := continuumBornPauliGreenScalarCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let bR := continuumBornPauliGreenXCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let bA := continuumBornPauliGreenXCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let dR := continuumBornPauliGreenZCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let dA := continuumBornPauliGreenZCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  ((Real.cos θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (bA * dR - bR * dA)

private def bornRaPauliXXCoefficient
    (v m p θ probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  let aR := continuumBornPauliGreenScalarCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let aA := continuumBornPauliGreenScalarCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let bR := continuumBornPauliGreenXCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let bA := continuumBornPauliGreenXCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let dR := continuumBornPauliGreenZCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let dA := continuumBornPauliGreenZCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  aR * aA - dR * dA +
    bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

private def bornRaPauliXYCoefficient
    (v m p θ probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  let aR := continuumBornPauliGreenScalarCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let aA := continuumBornPauliGreenScalarCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let bR := continuumBornPauliGreenXCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let bA := continuumBornPauliGreenXCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let dR := continuumBornPauliGreenZCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let dA := continuumBornPauliGreenZCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  Complex.I * (aA * dR - aR * dA) +
    2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)

private def bornRaPauliXZCoefficient
    (v m p θ probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  let aR := continuumBornPauliGreenScalarCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let aA := continuumBornPauliGreenScalarCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let bR := continuumBornPauliGreenXCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let bA := continuumBornPauliGreenXCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let dR := continuumBornPauliGreenZCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let dA := continuumBornPauliGreenZCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  ((Real.cos θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (aR * bA - aA * bR)

/-- Proof-only pointwise Pauli decomposition of the Born-dressed `Gᴿ σₓ Gᴬ` rung. -/
private theorem continuumBornRetardedAdvancedPauliX_polar_eq
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenMatrix .retarded v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar * sigmaX *
      continuumBornPauliGreenMatrix .advanced v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      bornRaPauliXScalarCoefficient v m p θ probeEnergy disorderStrength hbar • (1 : Matrix2) +
        bornRaPauliXXCoefficient v m p θ probeEnergy disorderStrength hbar • sigmaX +
        bornRaPauliXYCoefficient v m p θ probeEnergy disorderStrength hbar • sigmaY +
        bornRaPauliXZCoefficient v m p θ probeEnergy disorderStrength hbar • sigmaZ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [continuumBornPauliGreenMatrix, bornRaPauliXScalarCoefficient,
      bornRaPauliXXCoefficient, bornRaPauliXYCoefficient, bornRaPauliXZCoefficient,
      Matrix.mul_apply, continuumBornPauliGreenScalarCoefficient_polar,
      continuumBornPauliGreenXCoefficient_polar, continuumBornPauliGreenYCoefficient_polar,
      continuumBornPauliGreenZCoefficient_polar, sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

/-- Proof-only operator form of the pointwise Born-dressed Pauli decomposition. -/
private theorem continuumBornRetardedAdvancedPauliXOperator_polar_eq
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenOperator .retarded v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar *
      matrixOperator sigmaX *
      continuumBornPauliGreenOperator .advanced v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      bornRaPauliXScalarCoefficient v m p θ probeEnergy disorderStrength hbar •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        bornRaPauliXXCoefficient v m p θ probeEnergy disorderStrength hbar •
          matrixOperator sigmaX +
        bornRaPauliXYCoefficient v m p θ probeEnergy disorderStrength hbar •
          matrixOperator sigmaY +
        bornRaPauliXZCoefficient v m p θ probeEnergy disorderStrength hbar •
          matrixOperator sigmaZ := by
  unfold continuumBornPauliGreenOperator
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (continuumBornPauliGreenMatrix .retarded v m
          (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar) *
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaX *
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (continuumBornPauliGreenMatrix .advanced v m
          (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar) = _
  rw [← map_mul, ← map_mul, continuumBornRetardedAdvancedPauliX_polar_eq]
  simp [matrixOperator, map_add, map_smul]

/-- `σₓ` coefficient after the full polar-angle integral of the Born-dressed `Gᴿ σₓ Gᴬ` rung. -/
def continuumBornRetardedAdvancedPauliXAngularXCoefficient
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (continuumBornPauliGreenScalarCoefficient
        .retarded v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenScalarCoefficient
        .advanced v m p 0 probeEnergy disorderStrength hbar -
      continuumBornPauliGreenZCoefficient
        .retarded v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient
        .advanced v m p 0 probeEnergy disorderStrength hbar)

/-- Orientation-sensitive `σᵧ` coefficient after the full polar-angle integral of the Born-dressed
`Gᴿ σₓ Gᴬ` rung. The sign flips for `Gᴬ σₓ Gᴿ`. -/
def continuumBornRetardedAdvancedPauliXAngularYCoefficient
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) * Complex.I *
    (continuumBornPauliGreenScalarCoefficient
        .advanced v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient
        .retarded v m p 0 probeEnergy disorderStrength hbar -
      continuumBornPauliGreenScalarCoefficient
        .retarded v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient
        .advanced v m p 0 probeEnergy disorderStrength hbar)

/-- Full polar-angle Born-dressed Green-product rung at fixed radial momentum. -/
noncomputable def continuumBornAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    continuumBornPauliGreenOperator .retarded v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar *
      matrixOperator sigmaX *
      continuumBornPauliGreenOperator .advanced v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar

private theorem integral_bornRaPauliXScalarCoefficient_zero
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      bornRaPauliXScalarCoefficient v m p θ probeEnergy disorderStrength hbar) = 0 := by
  let cCos : ℂ :=
    continuumBornPauliGreenScalarCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenXCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar +
    continuumBornPauliGreenScalarCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenXCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar
  let cSin : ℂ := Complex.I *
    (continuumBornPauliGreenXCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar -
    continuumBornPauliGreenXCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar)
  have hcos : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun θ : ℝ => bornRaPauliXScalarCoefficient
      v m p θ probeEnergy disorderStrength hbar) =
      fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos +
        ((Real.sin θ : ℝ) : ℂ) * cSin by
    funext θ
    simp [bornRaPauliXScalarCoefficient, cCos, cSin]
    ring]
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp

private theorem integral_bornRaPauliXXCoefficient
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      bornRaPauliXXCoefficient v m p θ probeEnergy disorderStrength hbar) =
      continuumBornRetardedAdvancedPauliXAngularXCoefficient
        v m p probeEnergy disorderStrength hbar := by
  let c0 : ℂ :=
    continuumBornPauliGreenScalarCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenScalarCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar -
    continuumBornPauliGreenZCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar
  let c2 : ℂ :=
    continuumBornPauliGreenXCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenXCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar
  have hconst : IntervalIntegrable (fun _θ : ℝ => c0) volume 0 (2 * Real.pi) := by
    exact continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hosc : IntervalIntegrable
      (fun θ : ℝ =>
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun θ : ℝ => bornRaPauliXXCoefficient
      v m p θ probeEnergy disorderStrength hbar) =
      fun θ : ℝ => c0 +
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2 by
    funext θ
    simp [bornRaPauliXXCoefficient, c0, c2]
    ring]
  rw [intervalIntegral.integral_add hconst hosc,
    intervalIntegral.integral_mul_const, integral_complex_cos_sq_sub_sin_sq_zero_two_pi]
  simp [continuumBornRetardedAdvancedPauliXAngularXCoefficient, c0]
  ring

private theorem integral_bornRaPauliXYCoefficient
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      bornRaPauliXYCoefficient v m p θ probeEnergy disorderStrength hbar) =
      continuumBornRetardedAdvancedPauliXAngularYCoefficient
        v m p probeEnergy disorderStrength hbar := by
  let c0 : ℂ := Complex.I *
    (continuumBornPauliGreenScalarCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar -
    continuumBornPauliGreenScalarCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar)
  let c2 : ℂ :=
    2 * continuumBornPauliGreenXCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenXCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar
  have hconst : IntervalIntegrable (fun _θ : ℝ => c0) volume 0 (2 * Real.pi) := by
    exact continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hosc : IntervalIntegrable
      (fun θ : ℝ =>
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * c2)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hoscZero :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * c2) = 0 := by
    rw [intervalIntegral.integral_mul_const, integral_complex_cos_mul_sin_zero_two_pi]
    simp
  rw [show (fun θ : ℝ => bornRaPauliXYCoefficient
      v m p θ probeEnergy disorderStrength hbar) =
      fun θ : ℝ => c0 +
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * c2 by
    funext θ
    simp [bornRaPauliXYCoefficient, c0, c2]
    ring]
  rw [intervalIntegral.integral_add hconst hosc, hoscZero]
  simp [continuumBornRetardedAdvancedPauliXAngularYCoefficient, c0]
  ring

private theorem integral_bornRaPauliXZCoefficient_zero
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      bornRaPauliXZCoefficient v m p θ probeEnergy disorderStrength hbar) = 0 := by
  let cCos : ℂ :=
    continuumBornPauliGreenXCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar +
    continuumBornPauliGreenXCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenZCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar
  let cSin : ℂ := Complex.I *
    (continuumBornPauliGreenScalarCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenXCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar -
    continuumBornPauliGreenScalarCoefficient .advanced v m p 0
        probeEnergy disorderStrength hbar *
      continuumBornPauliGreenXCoefficient .retarded v m p 0
        probeEnergy disorderStrength hbar)
  have hcos : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun θ : ℝ => bornRaPauliXZCoefficient
      v m p θ probeEnergy disorderStrength hbar) =
      fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos +
        ((Real.sin θ : ℝ) : ℂ) * cSin by
    funext θ
    simp [bornRaPauliXZCoefficient, cCos, cSin]
    ring]
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp

/-- The full Born-dressed Green-product `x`-current rung closes exactly in the in-plane Pauli span. -/
theorem continuumBornAngularRetardedAdvancedPauliXIntegral_eq
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy disorderStrength hbar =
      continuumBornRetardedAdvancedPauliXAngularXCoefficient
          v m p probeEnergy disorderStrength hbar • matrixOperator sigmaX +
        continuumBornRetardedAdvancedPauliXAngularYCoefficient
          v m p probeEnergy disorderStrength hbar • matrixOperator sigmaY := by
  have hscalar : IntervalIntegrable
      (fun θ : ℝ => bornRaPauliXScalarCoefficient
        v m p θ probeEnergy disorderStrength hbar •
          (1 : DiracHilbert →L[ℂ] DiracHilbert)) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold bornRaPauliXScalarCoefficient
    fun_prop
  have hx : IntervalIntegrable
      (fun θ : ℝ => bornRaPauliXXCoefficient
        v m p θ probeEnergy disorderStrength hbar • matrixOperator sigmaX)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold bornRaPauliXXCoefficient
    fun_prop
  have hy : IntervalIntegrable
      (fun θ : ℝ => bornRaPauliXYCoefficient
        v m p θ probeEnergy disorderStrength hbar • matrixOperator sigmaY)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold bornRaPauliXYCoefficient
    fun_prop
  have hz : IntervalIntegrable
      (fun θ : ℝ => bornRaPauliXZCoefficient
        v m p θ probeEnergy disorderStrength hbar • matrixOperator sigmaZ)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold bornRaPauliXZCoefficient
    fun_prop
  unfold continuumBornAngularRetardedAdvancedPauliXIntegral
  rw [show (fun θ : ℝ =>
      continuumBornPauliGreenOperator .retarded v m
          (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar *
        matrixOperator sigmaX *
        continuumBornPauliGreenOperator .advanced v m
          (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar) =
      fun θ : ℝ =>
        bornRaPauliXScalarCoefficient v m p θ probeEnergy disorderStrength hbar •
            (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          bornRaPauliXXCoefficient v m p θ probeEnergy disorderStrength hbar •
            matrixOperator sigmaX +
          bornRaPauliXYCoefficient v m p θ probeEnergy disorderStrength hbar •
            matrixOperator sigmaY +
          bornRaPauliXZCoefficient v m p θ probeEnergy disorderStrength hbar •
            matrixOperator sigmaZ by
    funext θ
    exact continuumBornRetardedAdvancedPauliXOperator_polar_eq
      v m p θ probeEnergy disorderStrength hbar]
  rw [intervalIntegral.integral_add ((hscalar.add hx).add hy) hz,
    intervalIntegral.integral_add (hscalar.add hx) hy,
    intervalIntegral.integral_add hscalar hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [integral_bornRaPauliXScalarCoefficient_zero,
    integral_bornRaPauliXXCoefficient, integral_bornRaPauliXYCoefficient,
    integral_bornRaPauliXZCoefficient_zero]
  simp

/-- Real radial center of the Born retarded/advanced denominator pair. -/
def continuumBornRADenominatorCenter
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2) -
    v ^ 2 * p ^ 2

/-- Signed width parameter multiplying `i` in the retarded denominator. -/
def continuumBornRADenominatorWidth
    (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  2 * continuumBornDampingScale v disorderStrength hbar *
    (probeEnergy ^ 2 + m ^ 2)

/-- Manifestly real retarded-advanced denominator product. -/
def continuumBornRADenominatorProduct
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRADenominatorCenter v m p probeEnergy disorderStrength hbar ^ 2 +
    continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar ^ 2

/-- The real retarded-advanced denominator product is nonnegative. -/
theorem continuumBornRADenominatorProduct_nonneg
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    0 ≤ continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar := by
  unfold continuumBornRADenominatorProduct
  positivity

/-- The radial retarded/advanced denominator product is the real sum of squares `A(p)² + B²`. -/
theorem continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenDenominator
        .retarded v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenDenominator
        .advanced v m p 0 probeEnergy disorderStrength hbar =
      (continuumBornRADenominatorProduct
        v m p probeEnergy disorderStrength hbar : ℂ) := by
  rw [continuumBornPauliGreenDenominator_eq_closedForm .retarded,
    continuumBornPauliGreenDenominator_eq_closedForm .advanced]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  unfold continuumBornRADenominatorProduct continuumBornRADenominatorCenter
    continuumBornRADenominatorWidth
  simp only [SpectralSide.sign_retarded, SpectralSide.sign_advanced]
  push_cast
  ring_nf
  simp [hI]
  ring

/-- Closed Born `σₓ` angular coefficient before replacing the inverse denominator factors by their
real product. -/
theorem continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_inverseFactors
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularXCoefficient
        v m p probeEnergy disorderStrength hbar =
      (((2 * Real.pi *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornPauliGreenDenominator
          .retarded v m p 0 probeEnergy disorderStrength hbar)⁻¹ *
        (continuumBornPauliGreenDenominator
          .advanced v m p 0 probeEnergy disorderStrength hbar)⁻¹ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  unfold continuumBornRetardedAdvancedPauliXAngularXCoefficient
  unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenZCoefficient
  simp [continuumBornEffectiveEnergy, continuumBornEffectiveMass]
  ring_nf
  simp [hI]
  ring

/-- Closed Born `σᵧ` angular coefficient in repository orientation `Gᴿ σₓ Gᴬ`. -/
theorem continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_inverseFactors
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularYCoefficient
        v m p probeEnergy disorderStrength hbar =
      (((8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornPauliGreenDenominator
          .retarded v m p 0 probeEnergy disorderStrength hbar)⁻¹ *
        (continuumBornPauliGreenDenominator
          .advanced v m p 0 probeEnergy disorderStrength hbar)⁻¹ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  unfold continuumBornRetardedAdvancedPauliXAngularYCoefficient
  unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenZCoefficient
  simp [continuumBornEffectiveEnergy, continuumBornEffectiveMass]
  ring_nf
  simp [hI]

/-- Closed radial `σₓ` coefficient with the common real denominator product. -/
theorem continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularXCoefficient
        v m p probeEnergy disorderStrength hbar =
      (((2 * Real.pi *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_inverseFactors]
  rw [← continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq]
  simp [mul_inv_rev]
  ring

/-- Closed radial `σᵧ` coefficient with the common real denominator product. The positive sign is
specific to the repository orientation `Gᴿ σₓ Gᴬ`; `Gᴬ σₓ Gᴿ` has the opposite sign. -/
theorem continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularYCoefficient
        v m p probeEnergy disorderStrength hbar =
      (((8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_inverseFactors]
  rw [← continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq]
  simp [mul_inv_rev]
  ring

/-- Radial `σₓ` Green-product integrand after angular reduction, including only the polar Jacobian
`p dp`. The external disorder line and physical momentum-measure prefactor are not included. -/
def continuumBornRetardedAdvancedPauliXRadialXIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (p : ℂ) * continuumBornRetardedAdvancedPauliXAngularXCoefficient
    v m p probeEnergy disorderStrength hbar

/-- Radial `σᵧ` Green-product integrand after angular reduction, including only the polar Jacobian
`p dp`. The external disorder line and physical momentum-measure prefactor are not included. -/
def continuumBornRetardedAdvancedPauliXRadialYIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (p : ℂ) * continuumBornRetardedAdvancedPauliXAngularYCoefficient
    v m p probeEnergy disorderStrength hbar

/-- Closed real-denominator form of the radial `σₓ` Green-product integrand. -/
theorem continuumBornRetardedAdvancedPauliXRadialXIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialXIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((2 * Real.pi * p *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXRadialXIntegrand,
    continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_closed]
  push_cast
  ring

/-- Closed real-denominator form of the radial `σᵧ` Green-product integrand. -/
theorem continuumBornRetardedAdvancedPauliXRadialYIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((8 * Real.pi * p * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXRadialYIntegrand,
    continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_closed]
  push_cast
  ring

/-- External scalar-disorder line and physical-momentum measure factor for the continuum RA current
rung. The `2π` angle factor is already contained in the angular coefficients above, so this uses
`momentumMeasurePrefactor hbar` directly rather than `continuumBornAngularMeasurePrefactor hbar`. -/
def continuumBornRetardedAdvancedCurrentRungPrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

/-- Full continuum radial `σₓ` current-rung integrand, including the external disorder line and
physical momentum measure but not the radial integral. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
    continuumBornRetardedAdvancedPauliXRadialXIntegrand
      v m p probeEnergy disorderStrength hbar

/-- Full continuum radial `σᵧ` current-rung integrand, including the external disorder line and
physical momentum measure but not the radial integral. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
      v m p probeEnergy disorderStrength hbar

/-- Closed real-denominator form of the full radial `σₓ` current-rung integrand. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          2 * Real.pi * p *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand,
    continuumBornRetardedAdvancedPauliXRadialXIntegrand_eq_closed]
  push_cast
  ring

/-- Closed real-denominator form of the full radial `σᵧ` current-rung integrand. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          8 * Real.pi * p * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand,
    continuumBornRetardedAdvancedPauliXRadialYIntegrand_eq_closed]
  push_cast
  ring

end

end AnomalousHall.MassiveDirac