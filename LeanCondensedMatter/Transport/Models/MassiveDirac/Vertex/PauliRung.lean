import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Shared polar Pauli rung algebra

This file owns the model-specific `2 × 2` Pauli algebra common to the clean, Born-dressed, and
finite-broadening Born-Dyson retarded-advanced current rungs.  A rotationally symmetric massive-
Dirac propagator at fixed radial momentum has the polar form

```text
a I + b cos θ σₓ + b sin θ σᵧ + d σ_z.
```

For repository ordering `Gᴿ Γ Gᴬ`, the full-angle action on an arbitrary in-plane vertex
`Γ = α σₓ + β σᵧ` closes as

```text
(α, β) ↦ (X α - Y β, Y α + X β),
```

where `X` and `Y` depend only on the scalar and `σ_z` radial coefficients.  Concrete propagators
remain responsible for supplying those coefficients and for proving that their polar form matches
this shared algebra.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Polar Pauli matrix with a single radial in-plane coefficient. -/
def polarPauliMatrix (a b d : ℂ) (θ : ℝ) : Matrix2 :=
  a • (1 : Matrix2) +
    (((Real.cos θ : ℝ) : ℂ) * b) • sigmaX +
    (((Real.sin θ : ℝ) : ℂ) * b) • sigmaY +
    d • sigmaZ

/-- Bounded-operator realization of `polarPauliMatrix`. -/
noncomputable def polarPauliOperator (a b d : ℂ) (θ : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (polarPauliMatrix a b d θ)

/-- A Cartesian Pauli operator with one common denominator, angle-independent scalar and mass
numerators, and isotropic linear in-plane numerator reduces to `polarPauliOperator` after the polar
substitution `pₓ = p cos θ`, `pᵧ = p sin θ`. -/
theorem commonDenominatorPauliOperator_polar_eq
    (denominator energy mass : ℂ) (v p θ : ℝ) :
    matrixOperator
        ((denominator⁻¹ * energy) • (1 : Matrix2) +
          (denominator⁻¹ * ((v * (p * Real.cos θ) : ℝ) : ℂ)) • sigmaX +
          (denominator⁻¹ * ((v * (p * Real.sin θ) : ℝ) : ℂ)) • sigmaY +
          (denominator⁻¹ * mass) • sigmaZ) =
      polarPauliOperator
        (denominator⁻¹ * energy)
        (denominator⁻¹ * ((v * p : ℝ) : ℂ))
        (denominator⁻¹ * mass) θ := by
  unfold polarPauliOperator
  apply congrArg matrixOperator
  unfold polarPauliMatrix
  push_cast
  module

/-- Full-angle longitudinal coefficient of a retarded-advanced polar Pauli rung. -/
def pauliRungAngularXCoefficient (aR aA dR dA : ℂ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) * (aR * aA - dR * dA)

/-- Full-angle orientation-sensitive transverse coefficient of a retarded-advanced polar Pauli
rung. -/
def pauliRungAngularYCoefficient (aR aA dR dA : ℂ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) * Complex.I * (aA * dR - aR * dA)

private def polarRaInPlaneScalarCoefficient
    (aR aA bR bA dR dA alpha beta : ℂ) (θ : ℝ) : ℂ :=
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let common := aA * bR + aR * bA
  let skew := bA * dR - bR * dA
  alpha * (c * common + Complex.I * s * skew) +
    beta * (s * common - Complex.I * c * skew)

private def polarRaInPlaneXCoefficient
    (aR aA bR bA dR dA alpha beta : ℂ) (θ : ℝ) : ℂ :=
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let core := aR * aA - dR * dA
  let delta := aA * dR - aR * dA
  let quad := bR * bA * (c ^ 2 - s ^ 2)
  let mix := 2 * bR * bA * c * s
  alpha * (core + quad) + beta * ((-Complex.I) * delta + mix)

private def polarRaInPlaneYCoefficient
    (aR aA bR bA dR dA alpha beta : ℂ) (θ : ℝ) : ℂ :=
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let core := aR * aA - dR * dA
  let delta := aA * dR - aR * dA
  let quad := bR * bA * (c ^ 2 - s ^ 2)
  let mix := 2 * bR * bA * c * s
  alpha * (Complex.I * delta + mix) + beta * (core - quad)

private def polarRaInPlaneZCoefficient
    (aR aA bR bA dR dA alpha beta : ℂ) (θ : ℝ) : ℂ :=
  let c := ((Real.cos θ : ℝ) : ℂ)
  let s := ((Real.sin θ : ℝ) : ℂ)
  let sum := bA * dR + bR * dA
  let skew := aR * bA - aA * bR
  alpha * (c * sum + Complex.I * s * skew) +
    beta * (s * sum - Complex.I * c * skew)

private theorem polarPauliMatrix_mul_inPlane_mul_polarPauliMatrix
    (aR aA bR bA dR dA alpha beta : ℂ) (θ : ℝ) :
    polarPauliMatrix aR bR dR θ * (alpha • sigmaX + beta • sigmaY) *
        polarPauliMatrix aA bA dA θ =
      polarRaInPlaneScalarCoefficient aR aA bR bA dR dA alpha beta θ • (1 : Matrix2) +
        polarRaInPlaneXCoefficient aR aA bR bA dR dA alpha beta θ • sigmaX +
        polarRaInPlaneYCoefficient aR aA bR bA dR dA alpha beta θ • sigmaY +
        polarRaInPlaneZCoefficient aR aA bR bA dR dA alpha beta θ • sigmaZ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polarPauliMatrix, polarRaInPlaneScalarCoefficient,
      polarRaInPlaneXCoefficient, polarRaInPlaneYCoefficient,
      polarRaInPlaneZCoefficient, Matrix.mul_apply, sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

private theorem integral_polar_cos_sin_linear_zero (cCos cSin : ℂ) :
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
    integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp

private theorem integral_polar_inPlane_modes (c0 c2 cMix : ℂ) :
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

private theorem integral_polar_pauli_decomposition
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

/-- The full-angle retarded-advanced polar Pauli rung acts on in-plane coefficients by the
repository-oriented rotation matrix `[[X,-Y],[Y,X]]`. -/
theorem integral_polarPauliOperator_inPlane_eq
    (aR aA bR bA dR dA alpha beta : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarPauliOperator aR bR dR θ *
        matrixOperator (alpha • sigmaX + beta • sigmaY) *
        polarPauliOperator aA bA dA θ) =
      (pauliRungAngularXCoefficient aR aA dR dA * alpha -
        pauliRungAngularYCoefficient aR aA dR dA * beta) • matrixOperator sigmaX +
        (pauliRungAngularYCoefficient aR aA dR dA * alpha +
          pauliRungAngularXCoefficient aR aA dR dA * beta) • matrixOperator sigmaY := by
  let scalarCoefficient : ℝ → ℂ := fun θ =>
    polarRaInPlaneScalarCoefficient aR aA bR bA dR dA alpha beta θ
  let xCoefficient : ℝ → ℂ := fun θ =>
    polarRaInPlaneXCoefficient aR aA bR bA dR dA alpha beta θ
  let yCoefficient : ℝ → ℂ := fun θ =>
    polarRaInPlaneYCoefficient aR aA bR bA dR dA alpha beta θ
  let zCoefficient : ℝ → ℂ := fun θ =>
    polarRaInPlaneZCoefficient aR aA bR bA dR dA alpha beta θ
  have hpointwise :
      (fun θ : ℝ =>
        polarPauliOperator aR bR dR θ *
          matrixOperator (alpha • sigmaX + beta • sigmaY) *
          polarPauliOperator aA bA dA θ) =
      fun θ : ℝ =>
        scalarCoefficient θ • (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          xCoefficient θ • matrixOperator sigmaX +
          yCoefficient θ • matrixOperator sigmaY +
          zCoefficient θ • matrixOperator sigmaZ := by
    funext θ
    unfold polarPauliOperator
    change
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aR bR dR θ) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (alpha • sigmaX + beta • sigmaY) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aA bA dA θ) = _
    rw [← map_mul, ← map_mul,
      polarPauliMatrix_mul_inPlane_mul_polarPauliMatrix]
    simp [scalarCoefficient, xCoefficient, yCoefficient, zCoefficient,
      matrixOperator, map_add, map_smul]
  have hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = 0 := by
    convert integral_polar_cos_sin_linear_zero
      (alpha * (aA * bR + aR * bA) -
        beta * Complex.I * (bA * dR - bR * dA))
      (alpha * Complex.I * (bA * dR - bR * dA) +
        beta * (aA * bR + aR * bA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [scalarCoefficient, polarRaInPlaneScalarCoefficient]
    ring
  have hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) =
        pauliRungAngularXCoefficient aR aA dR dA * alpha -
          pauliRungAngularYCoefficient aR aA dR dA * beta := by
    convert integral_polar_inPlane_modes
      ((aR * aA - dR * dA) * alpha -
        Complex.I * (aA * dR - aR * dA) * beta)
      (bR * bA * alpha)
      (2 * bR * bA * beta) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [xCoefficient, polarRaInPlaneXCoefficient]
      ring
    · simp [pauliRungAngularXCoefficient, pauliRungAngularYCoefficient]
      ring
  have hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) =
        pauliRungAngularYCoefficient aR aA dR dA * alpha +
          pauliRungAngularXCoefficient aR aA dR dA * beta := by
    convert integral_polar_inPlane_modes
      (Complex.I * (aA * dR - aR * dA) * alpha +
        (aR * aA - dR * dA) * beta)
      (-(bR * bA * beta))
      (2 * bR * bA * alpha) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [yCoefficient, polarRaInPlaneYCoefficient]
      ring
    · simp [pauliRungAngularXCoefficient, pauliRungAngularYCoefficient]
      ring
  have hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = 0 := by
    convert integral_polar_cos_sin_linear_zero
      (alpha * (bA * dR + bR * dA) -
        beta * Complex.I * (aR * bA - aA * bR))
      (alpha * Complex.I * (aR * bA - aA * bR) +
        beta * (bA * dR + bR * dA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [zCoefficient, polarRaInPlaneZCoefficient]
    ring
  have hscalarContinuous : Continuous scalarCoefficient := by
    dsimp [scalarCoefficient, polarRaInPlaneScalarCoefficient]
    fun_prop
  have hxContinuous : Continuous xCoefficient := by
    dsimp [xCoefficient, polarRaInPlaneXCoefficient]
    fun_prop
  have hyContinuous : Continuous yCoefficient := by
    dsimp [yCoefficient, polarRaInPlaneYCoefficient]
    fun_prop
  have hzContinuous : Continuous zCoefficient := by
    dsimp [zCoefficient, polarRaInPlaneZCoefficient]
    fun_prop
  rw [hpointwise]
  rw [integral_polar_pauli_decomposition
    scalarCoefficient xCoefficient yCoefficient zCoefficient
    hscalarContinuous hxContinuous hyContinuous hzContinuous
    0
    (pauliRungAngularXCoefficient aR aA dR dA * alpha -
      pauliRungAngularYCoefficient aR aA dR dA * beta)
    (pauliRungAngularYCoefficient aR aA dR dA * alpha +
      pauliRungAngularXCoefficient aR aA dR dA * beta)
    0 hScalarIntegral hXIntegral hYIntegral hZIntegral]
  simp

end

end AnomalousHall.MassiveDirac
