import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson in-plane current-rung action

This module completes the fixed-radius angular reduction of the finite-external-broadening
Born-Dyson retarded-advanced current rung.  Together with the existing `σₓ` result, the `σᵧ` basis
rung is integrated over the full polar angle and the resulting two basis actions are assembled into
an arbitrary in-plane linear action.

For repository orientation `Gᴿ Γ Gᴬ`, the full-angle action is

```text
σₓ ↦  X σₓ + Y σᵧ,
σᵧ ↦ -Y σₓ + X σᵧ,
α σₓ + β σᵧ ↦ (X α - Y β) σₓ + (Y α + X β) σᵧ.
```

The coefficients `X` and `Y` are the actual finite-cutoff finite-`η` Born-Dyson angular
coefficients defined upstream.  Radial integration, scalar-disorder normalization, ladder
resummation, and broadening/disorder limits remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open scoped Interval

private theorem integral_finiteBornInPlane_complex_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.cos θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.cos)

private theorem integral_finiteBornInPlane_complex_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.sin)

private theorem integral_finiteBornInPlane_cos_sq_sub_sin_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2 - Real.sin θ ^ 2) = 0 := by
  simpa using
    (integral_cos_sq_sub_sin_sq (a := (0 : ℝ)) (b := 2 * Real.pi))

private theorem integral_finiteBornInPlane_complex_cos_sq_sub_sin_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℂ) ^ 2) - ((Real.sin θ : ℂ) ^ 2)) = 0 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((Real.cos θ : ℂ) ^ 2) - ((Real.sin θ : ℂ) ^ 2)) =
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          (((Real.cos θ ^ 2 - Real.sin θ ^ 2 : ℝ) : ℂ))) := by
            apply intervalIntegral.integral_congr
            intro θ _
            push_cast
            rfl
    _ = (((∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          Real.cos θ ^ 2 - Real.sin θ ^ 2) : ℝ) : ℂ) := by
            exact @intervalIntegral.integral_ofReal
              (0 : ℝ) (2 * Real.pi) volume
              (fun θ : ℝ => Real.cos θ ^ 2 - Real.sin θ ^ 2)
    _ = 0 := by
      rw [integral_finiteBornInPlane_cos_sq_sub_sin_sq_zero_two_pi]
      simp

private theorem integral_finiteBornInPlane_sin_mul_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ * Real.cos θ) = 0 := by
  simpa using
    (integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := 2 * Real.pi) 1 0)

private theorem integral_finiteBornInPlane_complex_cos_mul_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) =
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          (((Real.sin θ * Real.cos θ : ℝ) : ℂ))) := by
            apply intervalIntegral.integral_congr
            intro θ _
            push_cast
            ring
    _ = (((∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          Real.sin θ * Real.cos θ) : ℝ) : ℂ) := by
            exact @intervalIntegral.integral_ofReal
              (0 : ℝ) (2 * Real.pi) volume
              (fun θ : ℝ => Real.sin θ * Real.cos θ)
    _ = 0 := by
      rw [integral_finiteBornInPlane_sin_mul_cos_zero_two_pi]
      simp

/-- Full polar-angle `Gᴿ_B σᵧ Gᴬ_B` operator rung at fixed radial momentum, finite Born cutoff, and
finite external broadening. -/
noncomputable def finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax *
      matrixOperator sigmaY *
      finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax

/-- The full finite-`η` Born-Dyson `y`-current rung closes exactly in the in-plane Pauli span with
the orientation-sensitive rotation `σᵧ ↦ -Y σₓ + X σᵧ`. -/
theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
        v m p probeEnergy broadening disorderStrength hbar pMax =
      (-finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax) • matrixOperator sigmaX +
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaY := by
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
    ((Real.sin θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
      Complex.I * ((Real.cos θ : ℝ) : ℂ) * (bR * dA - bA * dR)
  let xCoefficient : ℝ → ℂ := fun θ =>
    (-Complex.I) * (aA * dR - aR * dA) +
      2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)
  let yCoefficient : ℝ → ℂ := fun θ =>
    aR * aA - dR * dA -
      bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))
  let zCoefficient : ℝ → ℂ := fun θ =>
    ((Real.sin θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
      Complex.I * ((Real.cos θ : ℝ) : ℂ) * (aA * bR - aR * bA)
  have hpointwise :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          matrixOperator sigmaY *
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
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaY *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (finiteCutoffContinuumBornDysonGreenMatrix
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) = _
    rw [← map_mul, ← map_mul, finiteCutoffContinuumBornDysonRetardedAdvancedPauliY_polar_eq]
    simp [matrixOperator, map_add, map_smul]
  have hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = 0 := by
    let cSin : ℂ := aA * bR + aR * bA
    let cCos : ℂ := Complex.I * (bR * dA - bA * dR)
    have hsin : IntervalIntegrable
        (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hcos : IntervalIntegrable
        (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show scalarCoefficient = fun θ : ℝ =>
        ((Real.sin θ : ℝ) : ℂ) * cSin + ((Real.cos θ : ℝ) : ℂ) * cCos by
      funext θ
      simp [scalarCoefficient, cSin, cCos]
      ring]
    rw [intervalIntegral.integral_add hsin hcos,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      integral_finiteBornInPlane_complex_sin_zero_two_pi,
      integral_finiteBornInPlane_complex_cos_zero_two_pi]
    simp
  have hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) =
        -finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax := by
    let c0 : ℂ := (-Complex.I) * (aA * dR - aR * dA)
    let c2 : ℂ := 2 * bR * bA
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
      rw [intervalIntegral.integral_mul_const,
        integral_finiteBornInPlane_complex_cos_mul_sin_zero_two_pi]
      simp
    rw [show xCoefficient = fun θ : ℝ =>
        c0 + (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * c2 by
      funext θ
      simp [xCoefficient, c0, c2]
      ring]
    rw [intervalIntegral.integral_add hconst hosc, hoscZero]
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
      aR, aA, dR, dA, c0]
    ring
  have hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) =
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax := by
    let c0 : ℂ := aR * aA - dR * dA
    let c2 : ℂ := -(bR * bA)
    have hconst : IntervalIntegrable (fun _θ : ℝ => c0) volume 0 (2 * Real.pi) := by
      exact continuous_const.intervalIntegrable 0 (2 * Real.pi)
    have hosc : IntervalIntegrable
        (fun θ : ℝ =>
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2)
        volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show yCoefficient = fun θ : ℝ =>
        c0 + ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2 by
      funext θ
      simp [yCoefficient, c0, c2]
      ring]
    rw [intervalIntegral.integral_add hconst hosc,
      intervalIntegral.integral_mul_const,
      integral_finiteBornInPlane_complex_cos_sq_sub_sin_sq_zero_two_pi]
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
      aR, aA, dR, dA, c0]
    ring
  have hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = 0 := by
    let cSin : ℂ := bA * dR + bR * dA
    let cCos : ℂ := Complex.I * (aA * bR - aR * bA)
    have hsin : IntervalIntegrable
        (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hcos : IntervalIntegrable
        (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show zCoefficient = fun θ : ℝ =>
        ((Real.sin θ : ℝ) : ℂ) * cSin + ((Real.cos θ : ℝ) : ℂ) * cCos by
      funext θ
      simp [zCoefficient, cSin, cCos]
      ring]
    rw [intervalIntegral.integral_add hsin hcos,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      integral_finiteBornInPlane_complex_sin_zero_two_pi,
      integral_finiteBornInPlane_complex_cos_zero_two_pi]
    simp
  have hscalar : IntervalIntegrable
      (fun θ : ℝ => scalarCoefficient θ • (1 : DiracHilbert →L[ℂ] DiracHilbert))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    dsimp [scalarCoefficient]
    fun_prop
  have hx : IntervalIntegrable
      (fun θ : ℝ => xCoefficient θ • matrixOperator sigmaX) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    dsimp [xCoefficient]
    fun_prop
  have hy : IntervalIntegrable
      (fun θ : ℝ => yCoefficient θ • matrixOperator sigmaY) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    dsimp [yCoefficient]
    fun_prop
  have hz : IntervalIntegrable
      (fun θ : ℝ => zCoefficient θ • matrixOperator sigmaZ) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    dsimp [zCoefficient]
    fun_prop
  unfold finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
  rw [hpointwise]
  rw [intervalIntegral.integral_add ((hscalar.add hx).add hy) hz,
    intervalIntegral.integral_add (hscalar.add hx) hy,
    intervalIntegral.integral_add hscalar hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [hScalarIntegral, hXIntegral, hYIntegral, hZIntegral]
  simp

/-- Full-angle finite-`η` Born-Dyson action induced on an arbitrary in-plane Pauli vertex.  The two
basis integrals are kept as the source of truth so no separate angular-rung approximation is
introduced here. -/
noncomputable def finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  alpha • finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
      v m p probeEnergy broadening disorderStrength hbar pMax +
    beta • finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
      v m p probeEnergy broadening disorderStrength hbar pMax

/-- The finite-`η` Born-Dyson full-angle rung acts on in-plane coefficients by the repository-oriented
rotation matrix `[[X,-Y],[Y,X]]`. -/
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
  unfold finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
  rw [finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral_eq,
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral_eq]
  module

@[simp] theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_one_zero
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
        v m p probeEnergy broadening disorderStrength hbar pMax 1 0 =
      finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening disorderStrength hbar pMax := by
  simp [finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction]

@[simp] theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_zero_one
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction
        v m p probeEnergy broadening disorderStrength hbar pMax 0 1 =
      finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliYIntegral
        v m p probeEnergy broadening disorderStrength hbar pMax := by
  simp [finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction]

end

end AnomalousHall.MassiveDirac
