import LeanCondensedMatter.Transport.Models.MassiveDirac.AngularReduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Angular reduction of the massive-Dirac retarded-advanced current rung

This Phase 5 entry point keeps the physical retarded-advanced ordering explicit while performing
only the model-specific `2 × 2` Pauli algebra. At fixed radial momentum it studies

```text
Gᴿ(p,θ) σₓ Gᴬ(p,θ)
```

before any radial integration, disorder normalization, zero-broadening limit, or ladder
resummation. The full polar-angle integral closes in the in-plane Pauli span. Reversing the
retarded/advanced order reverses the orientation-sensitive `σᵧ` term, so the order is not hidden by
a symmetric wrapper.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Matrix representative of the already-defined Pauli Green operator. This is only a finite
matrix adapter for explicit Pauli multiplication; it does not introduce a second Green-function
formalism. -/
def pauliGreenMatrix
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : Matrix2 :=
  pauliGreenScalarCoefficient side v m px py probeEnergy broadening • (1 : Matrix2) +
    pauliGreenXCoefficient side v m px py probeEnergy broadening • sigmaX +
    pauliGreenYCoefficient side v m px py probeEnergy broadening • sigmaY +
    pauliGreenZCoefficient side v m px py probeEnergy broadening • sigmaZ

/-- The matrix representative transports exactly to the canonical bounded Pauli Green operator. -/
theorem matrixOperator_pauliGreenMatrix
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    matrixOperator (pauliGreenMatrix side v m px py probeEnergy broadening) =
      pauliGreenOperator side v m px py probeEnergy broadening := by
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (pauliGreenMatrix side v m px py probeEnergy broadening) = _
  simp [pauliGreenMatrix, pauliGreenOperator, pauliGreenOperatorOfRegulator,
    pauliGreenScalarCoefficient, pauliGreenXCoefficient,
    pauliGreenYCoefficient, pauliGreenZCoefficient, matrixOperator, map_add, map_smul]

private def raPauliXScalarCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  ((Real.cos θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (bA * dR - bR * dA)

private def raPauliXXCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  aR * aA - dR * dA +
    bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

private def raPauliXYCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  Complex.I * (aA * dR - aR * dA) +
    2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)

private def raPauliXZCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  ((Real.cos θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (aR * bA - aA * bR)

/-- Exact pointwise Pauli decomposition of the repository-oriented `Gᴿ σₓ Gᴬ` rung in polar
coordinates. -/
theorem retardedAdvancedPauliX_polar_eq
    (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenMatrix .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * sigmaX *
      pauliGreenMatrix .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      raPauliXScalarCoefficient v m p θ probeEnergy broadening • (1 : Matrix2) +
        raPauliXXCoefficient v m p θ probeEnergy broadening • sigmaX +
        raPauliXYCoefficient v m p θ probeEnergy broadening • sigmaY +
        raPauliXZCoefficient v m p θ probeEnergy broadening • sigmaZ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliGreenMatrix, raPauliXScalarCoefficient, raPauliXXCoefficient,
      raPauliXYCoefficient, raPauliXZCoefficient, Matrix.mul_apply,
      pauliGreenScalarCoefficient_polar, pauliGreenXCoefficient_polar,
      pauliGreenYCoefficient_polar, pauliGreenZCoefficient_polar,
      sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

/-- Operator form of the exact pointwise Pauli decomposition, obtained by transporting the matrix
identity through the canonical matrix/operator equivalence. -/
theorem retardedAdvancedPauliXOperator_polar_eq
    (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * matrixOperator sigmaX *
      pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      raPauliXScalarCoefficient v m p θ probeEnergy broadening •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        raPauliXXCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaX +
        raPauliXYCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaY +
        raPauliXZCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaZ := by
  rw [← matrixOperator_pauliGreenMatrix, ← matrixOperator_pauliGreenMatrix]
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (pauliGreenMatrix .retarded v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening) *
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaX *
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (pauliGreenMatrix .advanced v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening) = _
  rw [← map_mul, ← map_mul, retardedAdvancedPauliX_polar_eq]
  simp [matrixOperator, map_add, map_smul]

/-- Radial `σₓ` coefficient after the full polar-angle average of `Gᴿ σₓ Gᴬ`. -/
def retardedAdvancedPauliXAngularXCoefficient
    (v m p probeEnergy broadening : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening -
      pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)

/-- Radial orientation-sensitive `σᵧ` coefficient after the full polar-angle average of
`Gᴿ σₓ Gᴬ`. -/
def retardedAdvancedPauliXAngularYCoefficient
    (v m p probeEnergy broadening : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) * Complex.I *
    (pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening -
      pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)

/-- Full polar-angle operator rung at fixed radial momentum. -/
noncomputable def continuumAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * matrixOperator sigmaX *
      pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening

private theorem integral_raPauliXScalarCoefficient_zero
    (v m p probeEnergy broadening : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      raPauliXScalarCoefficient v m p θ probeEnergy broadening) = 0 := by
  let cCos : ℂ :=
    pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening +
      pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let cSin : ℂ := Complex.I *
    (pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening -
      pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)
  have hcos : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun θ : ℝ => raPauliXScalarCoefficient v m p θ probeEnergy broadening) =
      fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos +
        ((Real.sin θ : ℝ) : ℂ) * cSin by
    funext θ
    simp [raPauliXScalarCoefficient, cCos, cSin]
    ring]
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp

private theorem integral_raPauliXXCoefficient
    (v m p probeEnergy broadening : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      raPauliXXCoefficient v m p θ probeEnergy broadening) =
      retardedAdvancedPauliXAngularXCoefficient v m p probeEnergy broadening := by
  let c0 : ℂ :=
    pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening -
      pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  let c2 : ℂ :=
    pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening *
      pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  have hconst : IntervalIntegrable (fun _θ : ℝ => c0) volume 0 (2 * Real.pi) := by
    exact continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hosc : IntervalIntegrable
      (fun θ : ℝ =>
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun θ : ℝ => raPauliXXCoefficient v m p θ probeEnergy broadening) =
      fun θ : ℝ => c0 +
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2 by
    funext θ
    simp [raPauliXXCoefficient, c0, c2]
    ring]
  rw [intervalIntegral.integral_add hconst hosc,
    intervalIntegral.integral_mul_const,
    integral_complex_cos_sq_sub_sin_sq_zero_two_pi]
  simp [retardedAdvancedPauliXAngularXCoefficient, c0]
  ring

private theorem integral_raPauliXYCoefficient
    (v m p probeEnergy broadening : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      raPauliXYCoefficient v m p θ probeEnergy broadening) =
      retardedAdvancedPauliXAngularYCoefficient v m p probeEnergy broadening := by
  let c0 : ℂ := Complex.I *
    (pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening -
      pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)
  let c2 : ℂ :=
    2 * pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening *
      pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
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
  rw [show (fun θ : ℝ => raPauliXYCoefficient v m p θ probeEnergy broadening) =
      fun θ : ℝ => c0 +
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * c2 by
    funext θ
    simp [raPauliXYCoefficient, c0, c2]
    ring]
  rw [intervalIntegral.integral_add hconst hosc, hoscZero]
  simp [retardedAdvancedPauliXAngularYCoefficient, c0]
  ring

private theorem integral_raPauliXZCoefficient_zero
    (v m p probeEnergy broadening : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      raPauliXZCoefficient v m p θ probeEnergy broadening) = 0 := by
  let cCos : ℂ :=
    pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening +
      pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  let cSin : ℂ := Complex.I *
    (pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening -
      pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening)
  have hcos : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) * cSin) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun θ : ℝ => raPauliXZCoefficient v m p θ probeEnergy broadening) =
      fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) * cCos +
        ((Real.sin θ : ℝ) : ℂ) * cSin by
    funext θ
    simp [raPauliXZCoefficient, cCos, cSin]
    ring]
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp

/-- The full retarded-advanced `x`-current rung closes exactly in the in-plane Pauli span. The
identity and `σ_z` channels vanish under the full polar-angle integral. -/
theorem continuumAngularRetardedAdvancedPauliXIntegral_eq
    (v m p probeEnergy broadening : ℝ) :
    continuumAngularRetardedAdvancedPauliXIntegral v m p probeEnergy broadening =
      retardedAdvancedPauliXAngularXCoefficient v m p probeEnergy broadening •
          matrixOperator sigmaX +
        retardedAdvancedPauliXAngularYCoefficient v m p probeEnergy broadening •
          matrixOperator sigmaY := by
  have hscalar : IntervalIntegrable
      (fun θ : ℝ =>
        raPauliXScalarCoefficient v m p θ probeEnergy broadening •
          (1 : DiracHilbert →L[ℂ] DiracHilbert)) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold raPauliXScalarCoefficient
    fun_prop
  have hx : IntervalIntegrable
      (fun θ : ℝ =>
        raPauliXXCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaX)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold raPauliXXCoefficient
    fun_prop
  have hy : IntervalIntegrable
      (fun θ : ℝ =>
        raPauliXYCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaY)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold raPauliXYCoefficient
    fun_prop
  have hz : IntervalIntegrable
      (fun θ : ℝ =>
        raPauliXZCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaZ)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold raPauliXZCoefficient
    fun_prop
  unfold continuumAngularRetardedAdvancedPauliXIntegral
  rw [show (fun θ : ℝ =>
      pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening * matrixOperator sigmaX *
        pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening) =
      fun θ : ℝ =>
        raPauliXScalarCoefficient v m p θ probeEnergy broadening •
            (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          raPauliXXCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaX +
          raPauliXYCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaY +
          raPauliXZCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaZ by
    funext θ
    exact retardedAdvancedPauliXOperator_polar_eq v m p θ probeEnergy broadening]
  rw [intervalIntegral.integral_add ((hscalar.add hx).add hy) hz,
    intervalIntegral.integral_add (hscalar.add hx) hy,
    intervalIntegral.integral_add hscalar hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [integral_raPauliXScalarCoefficient_zero,
    integral_raPauliXXCoefficient, integral_raPauliXYCoefficient,
    integral_raPauliXZCoefficient_zero]
  simp

end

end MassiveDirac
end AnomalousHall
