import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexAngular
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Full-angle finite-broadening Born-Dyson current rung

This module integrates the pointwise finite-`η` Born-Dyson Pauli products from
`FiniteBroadeningCurrentVertexAngular.lean` over the full polar angle.  Radial momentum remains
fixed; the scalar-disorder line, momentum measure, radial integration, and ladder fixed point are
not part of this layer.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open scoped Interval

private theorem integral_finiteBorn_complex_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.cos θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.cos)

private theorem integral_finiteBorn_complex_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.sin)

private theorem integral_finiteBorn_cos_sq_sub_sin_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2 - Real.sin θ ^ 2) = 0 := by
  simpa using
    (integral_cos_sq_sub_sin_sq (a := (0 : ℝ)) (b := 2 * Real.pi))

private theorem integral_finiteBorn_complex_cos_sq_sub_sin_sq_zero_two_pi :
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
    _ = 0 := by rw [integral_finiteBorn_cos_sq_sub_sin_sq_zero_two_pi]; simp

private theorem integral_finiteBorn_sin_mul_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ * Real.cos θ) = 0 := by
  simpa using
    (integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := 2 * Real.pi) 1 0)

private theorem integral_finiteBorn_complex_cos_mul_sin_zero_two_pi :
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
    _ = 0 := by rw [integral_finiteBorn_sin_mul_cos_zero_two_pi]; simp

/-- Full polar-angle `Gᴿ_B σₓ Gᴬ_B` operator rung at fixed radial momentum, finite Born cutoff, and
finite external broadening. -/
noncomputable def finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax *
      matrixOperator sigmaX *
      finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax

/-- The full finite-`η` Born-Dyson `x`-current rung closes exactly in the in-plane Pauli span. -/
theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaX +
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
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
    ((Real.cos θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
      Complex.I * ((Real.sin θ : ℝ) : ℂ) * (bA * dR - bR * dA)
  let xCoefficient : ℝ → ℂ := fun θ =>
    aR * aA - dR * dA +
      bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))
  let yCoefficient : ℝ → ℂ := fun θ =>
    Complex.I * (aA * dR - aR * dA) +
      2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)
  let zCoefficient : ℝ → ℂ := fun θ =>
    ((Real.cos θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
      Complex.I * ((Real.sin θ : ℝ) : ℂ) * (aR * bA - aA * bR)
  have hpointwise :
      (fun θ : ℝ =>
        finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          matrixOperator sigmaX *
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
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaX *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (finiteCutoffContinuumBornDysonGreenMatrix
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) = _
    rw [← map_mul, ← map_mul, finiteCutoffContinuumBornDysonRetardedAdvancedPauliX_polar_eq]
    simp [matrixOperator, map_add, map_smul]
  have hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = 0 := by
    let cCos : ℂ := aA * bR + aR * bA
    let cSin : ℂ := Complex.I * (bA * dR - bR * dA)
    have hcos : IntervalIntegrable
        (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hsin : IntervalIntegrable
        (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show scalarCoefficient = fun θ : ℝ =>
        ((Real.cos θ : ℝ) : ℂ) * cCos + ((Real.sin θ : ℝ) : ℂ) * cSin by
      funext θ
      simp [scalarCoefficient, cCos, cSin]
      ring]
    rw [intervalIntegral.integral_add hcos hsin,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      integral_finiteBorn_complex_cos_zero_two_pi,
      integral_finiteBorn_complex_sin_zero_two_pi]
    simp
  have hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) =
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax := by
    let c0 : ℂ := aR * aA - dR * dA
    let c2 : ℂ := bR * bA
    have hconst : IntervalIntegrable (fun _θ : ℝ => c0) volume 0 (2 * Real.pi) := by
      exact continuous_const.intervalIntegrable 0 (2 * Real.pi)
    have hosc : IntervalIntegrable
        (fun θ : ℝ =>
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2)
        volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show xCoefficient = fun θ : ℝ =>
        c0 + ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2 by
      funext θ
      simp [xCoefficient, c0, c2]
      ring]
    rw [intervalIntegral.integral_add hconst hosc,
      intervalIntegral.integral_mul_const,
      integral_finiteBorn_complex_cos_sq_sub_sin_sq_zero_two_pi]
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
      aR, aA, dR, dA, c0]
    ring
  have hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) =
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax := by
    let c0 : ℂ := Complex.I * (aA * dR - aR * dA)
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
        integral_finiteBorn_complex_cos_mul_sin_zero_two_pi]
      simp
    rw [show yCoefficient = fun θ : ℝ =>
        c0 + (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * c2 by
      funext θ
      simp [yCoefficient, c0, c2]
      ring]
    rw [intervalIntegral.integral_add hconst hosc, hoscZero]
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
      aR, aA, dR, dA, c0]
    ring
  have hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = 0 := by
    let cCos : ℂ := bA * dR + bR * dA
    let cSin : ℂ := Complex.I * (aR * bA - aA * bR)
    have hcos : IntervalIntegrable
        (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hsin : IntervalIntegrable
        (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show zCoefficient = fun θ : ℝ =>
        ((Real.cos θ : ℝ) : ℂ) * cCos + ((Real.sin θ : ℝ) : ℂ) * cSin by
      funext θ
      simp [zCoefficient, cCos, cSin]
      ring]
    rw [intervalIntegral.integral_add hcos hsin,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      integral_finiteBorn_complex_cos_zero_two_pi,
      integral_finiteBorn_complex_sin_zero_two_pi]
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
  unfold finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
  rw [hpointwise]
  rw [intervalIntegral.integral_add ((hscalar.add hx).add hy) hz,
    intervalIntegral.integral_add (hscalar.add hx) hy,
    intervalIntegral.integral_add hscalar hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [hScalarIntegral, hXIntegral, hYIntegral, hZIntegral]
  simp

end

end AnomalousHall.MassiveDirac
