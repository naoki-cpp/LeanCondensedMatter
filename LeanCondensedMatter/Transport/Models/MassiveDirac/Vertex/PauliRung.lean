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

where `X` and `Y` depend only on the scalar and `σ_z` radial coefficients. The pointwise Pauli
sandwich supplies the generic `AngularHarmonicCoefficients Matrix2` representation shared by
ordinary and Fourier-weighted angular reduction. Concrete propagators remain responsible for
supplying the radial coefficients.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Direction-indexed full-angle coefficient vector of a retarded-advanced polar Pauli rung. -/
def pauliRungAngularCoefficient (aR aA dR dA : ℂ) : Fin 2 → ℂ :=
  ![(((2 * Real.pi : ℝ) : ℂ)) * (aR * aA - dR * dA),
    (((2 * Real.pi : ℝ) : ℂ)) * Complex.I * (aA * dR - aR * dA)]

/-- Constant, first, and second angular harmonics of
`polarPauliMatrix aL bL dL θ * Γ * polarPauliMatrix aR bR dR θ` for an arbitrary in-plane `Γ`. -/
def polarPauliInPlaneHarmonics
    (aL bL dL aR bR dR : ℂ) (coefficients : InPlaneCoefficientVector) :
    AngularHarmonicCoefficients Matrix2 :=
  let c0 := aL * aR - dL * dR
  let cxy := Complex.I * (aR * dL - aL * dR)
  let scalar := aR * bL + aL * bR
  let scalarMix := bR * dL - bL * dR
  let mass := bR * dL + bL * dR
  let massMix := aL * bR - aR * bL
  {
    constant :=
      (c0 * coefficients 0 - cxy * coefficients 1) • sigmaX +
        (cxy * coefficients 0 + c0 * coefficients 1) • sigmaY
    firstCosine :=
      (scalar * coefficients 0 - Complex.I * scalarMix * coefficients 1) • (1 : Matrix2) +
        (mass * coefficients 0 - Complex.I * massMix * coefficients 1) • sigmaZ
    firstSine :=
      (Complex.I * scalarMix * coefficients 0 + scalar * coefficients 1) • (1 : Matrix2) +
        (Complex.I * massMix * coefficients 0 + mass * coefficients 1) • sigmaZ
    secondCosine :=
      (bL * bR * coefficients 0) • sigmaX -
        (bL * bR * coefficients 1) • sigmaY
    secondMixed :=
      (2 * bL * bR * coefficients 1) • sigmaX +
        (2 * bL * bR * coefficients 0) • sigmaY
  }

/-- Pointwise decomposition of a polar-Pauli sandwich into the canonical constant, first, and second
angular-harmonic evaluation used by ordinary and Fourier-weighted reduction. -/
theorem polarPauliMatrix_inPlane_sandwich_eq_harmonics
    (aL bL dL aR bR dR : ℂ) (coefficients : InPlaneCoefficientVector) (θ : ℝ) :
    polarPauliMatrix aL bL dL θ *
        (coefficients 0 • sigmaX + coefficients 1 • sigmaY) *
        polarPauliMatrix aR bR dR θ =
      (polarPauliInPlaneHarmonics aL bL dL aR bR dR coefficients).eval θ := by
  let uL : PauliAxis → ℂ
    | .x => ((Real.cos θ : ℝ) : ℂ) * bL
    | .y => ((Real.sin θ : ℝ) : ℂ) * bL
    | .z => dL
  let uR : PauliAxis → ℂ
    | .x => ((Real.cos θ : ℝ) : ℂ) * bR
    | .y => ((Real.sin θ : ℝ) : ℂ) * bR
    | .z => dR
  let vertex : PauliAxis → ℂ
    | .x => coefficients 0
    | .y => coefficients 1
    | .z => 0
  have hL :
      polarPauliMatrix aL bL dL θ =
        aL • (1 : Matrix2) + InternalSpace.pauliCombination uL := by
    simp [polarPauliMatrix, uL, InternalSpace.pauliCombination]
    module
  have hR :
      polarPauliMatrix aR bR dR θ =
        aR • (1 : Matrix2) + InternalSpace.pauliCombination uR := by
    simp [polarPauliMatrix, uR, InternalSpace.pauliCombination]
    module
  have hVertex :
      coefficients 0 • sigmaX + coefficients 1 • sigmaY =
        (0 : ℂ) • (1 : Matrix2) + InternalSpace.pauliCombination vertex := by
    simp [vertex, InternalSpace.pauliCombination]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  rw [hL, hVertex, hR,
    InternalSpace.pauliAffine_mul_pauliAffine,
    InternalSpace.pauliAffine_mul_pauliAffine]
  simp [uL, uR, vertex, InternalSpace.pauliCross, cross_apply,
    InternalSpace.pauliAxisComponent, InternalSpace.dotProduct_pauliAxis,
    InternalSpace.pauliCombination, polarPauliInPlaneHarmonics,
    AngularHarmonicCoefficients.eval]
  ring_nf
  simp [hI]
  module

private theorem integral_polar_inPlane_modes (c0 c2 cMix : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      c0 +
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * c2 +
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * cMix) =
      (((2 * Real.pi : ℝ) : ℂ)) * c0 := by
  let harmonics : AngularHarmonicCoefficients ℂ :=
    { constant := c0
      firstCosine := 0
      firstSine := 0
      secondCosine := c2
      secondMixed := cMix }
  simpa [harmonics, AngularHarmonicCoefficients.eval, smul_eq_mul] using harmonics.integral_eval

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
    coefficients 0 * (c * (aA * bR + aR * bA) + Complex.I * s * (bA * dR - bR * dA)) +
      coefficients 1 * (s * (aA * bR + aR * bA) - Complex.I * c * (bA * dR - bR * dA))
  let xCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients 0 * (aR * aA - dR * dA + bR * bA * (c ^ 2 - s ^ 2)) +
      coefficients 1 * ((-Complex.I) * (aA * dR - aR * dA) + 2 * bR * bA * c * s)
  let yCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients 0 * (Complex.I * (aA * dR - aR * dA) + 2 * bR * bA * c * s) +
      coefficients 1 * (aR * aA - dR * dA - bR * bA * (c ^ 2 - s ^ 2))
  let zCoefficient : ℝ → ℂ := fun θ =>
    let c := ((Real.cos θ : ℝ) : ℂ)
    let s := ((Real.sin θ : ℝ) : ℂ)
    coefficients 0 * (c * (bA * dR + bR * dA) + Complex.I * s * (aR * bA - aA * bR)) +
      coefficients 1 * (s * (bA * dR + bR * dA) - Complex.I * c * (aR * bA - aA * bR))
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
    have hmatrix :
        polarPauliMatrix aR bR dR θ *
            (coefficients 0 • sigmaX + coefficients 1 • sigmaY) *
            polarPauliMatrix aA bA dA θ =
          scalarCoefficient θ • (1 : Matrix2) +
            xCoefficient θ • sigmaX +
            yCoefficient θ • sigmaY +
            zCoefficient θ • sigmaZ := by
      rw [polarPauliMatrix_inPlane_sandwich_eq_harmonics]
      simp [polarPauliInPlaneHarmonics, AngularHarmonicCoefficients.eval,
        scalarCoefficient, xCoefficient, yCoefficient, zCoefficient]
      module
    have hVertexOperator :
        coefficients 0 • matrixOperator sigmaX + coefficients 1 • matrixOperator sigmaY =
          matrixOperator (coefficients 0 • sigmaX + coefficients 1 • sigmaY) := by
      simp [matrixOperator]
    unfold inPlanePauliVertexOperator polarPauliOperator
    rw [hVertexOperator]
    change
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aR bR dR θ) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (coefficients 0 • sigmaX + coefficients 1 • sigmaY) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aA bA dA θ) = _
    rw [← map_mul, ← map_mul, hmatrix]
    simp [matrixOperator, map_add, map_smul]
  have hScalarIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), scalarCoefficient θ) = 0 := by
    convert integral_complex_cos_mul_add_sin_mul_zero_two_pi
      (coefficients 0 * (aA * bR + aR * bA) -
        coefficients 1 * Complex.I * (bA * dR - bR * dA))
      (coefficients 0 * Complex.I * (bA * dR - bR * dA) +
        coefficients 1 * (aA * bR + aR * bA)) using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [scalarCoefficient]
    ring
  have hXIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), xCoefficient θ) =
        pauliRungAngularCoefficient aR aA dR dA 0 * coefficients 0 -
          pauliRungAngularCoefficient aR aA dR dA 1 * coefficients 1 := by
    convert integral_polar_inPlane_modes
      ((aR * aA - dR * dA) * coefficients 0 -
        Complex.I * (aA * dR - aR * dA) * coefficients 1)
      (bR * bA * coefficients 0)
      (2 * bR * bA * coefficients 1) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [xCoefficient]
      ring
    · simp [pauliRungAngularCoefficient]
      ring
  have hYIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), yCoefficient θ) =
        pauliRungAngularCoefficient aR aA dR dA 1 * coefficients 0 +
          pauliRungAngularCoefficient aR aA dR dA 0 * coefficients 1 := by
    convert integral_polar_inPlane_modes
      (Complex.I * (aA * dR - aR * dA) * coefficients 0 +
        (aR * aA - dR * dA) * coefficients 1)
      (-(bR * bA * coefficients 1))
      (2 * bR * bA * coefficients 0) using 1
    · apply intervalIntegral.integral_congr
      intro θ _
      simp [yCoefficient]
      ring
    · simp [pauliRungAngularCoefficient]
      ring
  have hZIntegral :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), zCoefficient θ) = 0 := by
    convert integral_complex_cos_mul_add_sin_mul_zero_two_pi
      (coefficients 0 * (bA * dR + bR * dA) -
        coefficients 1 * Complex.I * (aR * bA - aA * bR))
      (coefficients 0 * Complex.I * (aR * bA - aA * bR) +
        coefficients 1 * (bA * dR + bR * dA)) using 1
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
