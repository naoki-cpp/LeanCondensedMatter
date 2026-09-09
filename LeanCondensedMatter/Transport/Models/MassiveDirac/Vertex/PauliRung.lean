import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.InPlaneLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Shared polar Pauli rung algebra

This file owns the model-specific `2 × 2` Pauli rung algebra common to the clean, Born-dressed, and
finite-broadening Born-Dyson retarded-advanced current rungs. The shared polar Pauli matrix/operator
representation itself is owned upstream by `Model.Operator`. For repository ordering `Gᴿ Γ Gᴬ`, the
full-angle action on an arbitrary in-plane vertex `Γ = α σₓ + β σᵧ` closes as

```text
(α, β) ↦ (X α - Y β, Y α + X β),
```

where `X` and `Y` depend only on the scalar and `σ_z` radial coefficients. Concrete propagators
remain responsible for supplying those coefficients and for proving that their polar form matches
the shared model representation.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Direction-indexed full-angle coefficient vector of a retarded-advanced polar Pauli rung. -/
def pauliRungAngularCoefficient (aR aA dR dA : ℂ) : Direction2 → ℂ
  | .x => (((2 * Real.pi : ℝ) : ℂ)) * (aR * aA - dR * dA)
  | .y => (((2 * Real.pi : ℝ) : ℂ)) * Complex.I * (aA * dR - aR * dA)

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

/-- The full-angle retarded-advanced polar Pauli rung acts through the canonical in-plane ladder
action, preserving the complete coefficient vector until the operator boundary. -/
theorem integral_polarPauliOperator_inPlane_eq
    (aR aA bR bA dR dA : ℂ) (coefficients : InPlaneCoefficientVector) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarPauliOperator aR bR dR θ *
        inPlanePauliVertexOperator coefficients *
        polarPauliOperator aA bA dA θ) =
      inPlanePauliVertexOperator
        (inPlaneLadderAction (pauliRungAngularCoefficient aR aA dR dA) coefficients) := by
  let scalarCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients .x * (c * (aA * bR + aR * bA) + Complex.I * s * (bA * dR - bR * dA)) +
      coefficients .y * (s * (aA * bR + aR * bA) - Complex.I * c * (bA * dR - bR * dA))
  let xCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients .x * (aR * aA - dR * dA + bR * bA * (c ^ 2 - s ^ 2)) +
      coefficients .y * ((-Complex.I) * (aA * dR - aR * dA) + 2 * bR * bA * c * s)
  let yCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients .x * (Complex.I * (aA * dR - aR * dA) + 2 * bR * bA * c * s) +
      coefficients .y * (aR * aA - dR * dA - bR * bA * (c ^ 2 - s ^ 2))
  let zCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients .x * (c * (bA * dR + bR * dA) + Complex.I * s * (aR * bA - aA * bR)) +
      coefficients .y * (s * (bA * dR + bR * dA) - Complex.I * c * (aR * bA - aA * bR))
  have hpointwise :
      (fun θ : ℝ =>
        polarPauliOperator aR bR dR θ *
          inPlanePauliVertexOperator coefficients *
          polarPauliOperator aA bA dA θ) =
      fun θ : ℝ =>
        scalarCoefficient θ • (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          xCoefficient θ • matrixOperator sigmaX +
          yCoefficient θ • matrixOperator sigmaY +
          zCoefficient θ • matrixOperator sigmaZ := by
    funext θ
    unfold inPlanePauliVertexOperator
    let uR : PauliAxis → ℂ
      | .x => ((Real.cos θ : ℝ) : ℂ) * bR
      | .y => ((Real.sin θ : ℝ) : ℂ) * bR
      | .z => dR
    let uA : PauliAxis → ℂ
      | .x => ((Real.cos θ : ℝ) : ℂ) * bA
      | .y => ((Real.sin θ : ℝ) : ℂ) * bA
      | .z => dA
    let vertex : PauliAxis → ℂ
      | .x => coefficients .x
      | .y => coefficients .y
      | .z => 0
    have hR :
        polarPauliMatrix aR bR dR θ =
          aR • (1 : Matrix2) + InternalSpace.pauliCombination uR := by
      simp [polarPauliMatrix, uR, InternalSpace.pauliCombination]
      module
    have hA :
        polarPauliMatrix aA bA dA θ =
          aA • (1 : Matrix2) + InternalSpace.pauliCombination uA := by
      simp [polarPauliMatrix, uA, InternalSpace.pauliCombination]
      module
    have hVertex :
        coefficients .x • sigmaX + coefficients .y • sigmaY =
          (0 : ℂ) • (1 : Matrix2) + InternalSpace.pauliCombination vertex := by
      simp [vertex, InternalSpace.pauliCombination]
    have hI : Complex.I ^ 2 = (-1 : ℂ) := by
      simpa [pow_two] using Complex.I_mul_I
    have hmatrix :
        polarPauliMatrix aR bR dR θ *
            (coefficients .x • sigmaX + coefficients .y • sigmaY) *
            polarPauliMatrix aA bA dA θ =
          scalarCoefficient θ • (1 : Matrix2) +
            xCoefficient θ • sigmaX +
            yCoefficient θ • sigmaY +
            zCoefficient θ • sigmaZ := by
      rw [hR, hVertex, hA,
        InternalSpace.pauliAffine_mul_pauliAffine,
        InternalSpace.pauliAffine_mul_pauliAffine]
      simp [uR, uA, vertex, InternalSpace.pauliCross, InternalSpace.dotProduct_pauliAxis,
        InternalSpace.pauliCombination, scalarCoefficient, xCoefficient, yCoefficient, zCoefficient]
      ring_nf
      simp [hI]
      module
    unfold polarPauliOperator
    change
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aR bR dR θ) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (coefficients .x • sigmaX + coefficients .y • sigmaY) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aA bA dA θ) = _
    rw [← map_mul, ← map_mul, hmatrix]
    simp [matrixOperator, map_add, map_smul]
  have hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = 0 := by
    convert integral_polar_cos_sin_linear_zero
      (coefficients .x * (aA * bR + aR * bA) -
        coefficients .y * Complex.I * (bA * dR - bR * dA))
      (coefficients .x * Complex.I * (bA * dR - bR * dA) +
        coefficients .y * (aA * bR + aR * bA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [scalarCoefficient]
    ring
  have hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) =
        pauliRungAngularCoefficient aR aA dR dA .x * coefficients .x -
          pauliRungAngularCoefficient aR aA dR dA .y * coefficients .y := by
    convert integral_polar_inPlane_modes
      ((aR * aA - dR * dA) * coefficients .x -
        Complex.I * (aA * dR - aR * dA) * coefficients .y)
      (bR * bA * coefficients .x)
      (2 * bR * bA * coefficients .y) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [xCoefficient]
      ring
    · simp [pauliRungAngularCoefficient]
      ring
  have hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) =
        pauliRungAngularCoefficient aR aA dR dA .y * coefficients .x +
          pauliRungAngularCoefficient aR aA dR dA .x * coefficients .y := by
    convert integral_polar_inPlane_modes
      (Complex.I * (aA * dR - aR * dA) * coefficients .x +
        (aR * aA - dR * dA) * coefficients .y)
      (-(bR * bA * coefficients .y))
      (2 * bR * bA * coefficients .x) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [yCoefficient]
      ring
    · simp [pauliRungAngularCoefficient]
      ring
  have hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = 0 := by
    convert integral_polar_cos_sin_linear_zero
      (coefficients .x * (bA * dR + bR * dA) -
        coefficients .y * Complex.I * (aR * bA - aA * bR))
      (coefficients .x * Complex.I * (aR * bA - aA * bR) +
        coefficients .y * (bA * dR + bR * dA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [zCoefficient]
    ring
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
  rw [hpointwise]
  rw [intervalIntegral.integral_add ((hscalar.add hx).add hy) hz,
    intervalIntegral.integral_add (hscalar.add hx) hy,
    intervalIntegral.integral_add hscalar hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [hScalarIntegral, hXIntegral, hYIntegral, hZIntegral]
  simp [inPlanePauliVertexOperator]

end

end QuantumTheory.Transport.Models.MassiveDirac
