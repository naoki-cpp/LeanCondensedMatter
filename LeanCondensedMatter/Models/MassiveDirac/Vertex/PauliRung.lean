import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Models.MassiveDirac.Vertex.InPlaneLadder
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

namespace QuantumTheory.Models.MassiveDirac

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
    simp [polarPauliMatrix, uL, InternalSpace.pauliCombination_eq_components]
    module
  have hR :
      polarPauliMatrix aR bR dR θ =
        aR • (1 : Matrix2) + InternalSpace.pauliCombination uR := by
    simp [polarPauliMatrix, uR, InternalSpace.pauliCombination_eq_components]
    module
  have hVertex :
      coefficients 0 • sigmaX + coefficients 1 • sigmaY =
        (0 : ℂ) • (1 : Matrix2) + InternalSpace.pauliCombination vertex := by
    simp [vertex, InternalSpace.pauliCombination_eq_components]
  rw [hL, hVertex, hR,
    InternalSpace.pauliAffine_mul_pauliAffine,
    InternalSpace.pauliAffine_mul_pauliAffine]
  simp [uL, uR, vertex, InternalSpace.pauliCross, cross_apply,
    InternalSpace.pauliAxisComponent, InternalSpace.dotProduct_pauliAxis,
    InternalSpace.pauliCombination_eq_components, polarPauliInPlaneHarmonics,
    AngularHarmonicCoefficients.eval]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  ring_nf
  simp [hI]
  module

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
  let H := polarPauliInPlaneHarmonics aR bR dR aA bA dA coefficients
  let HO : AngularHarmonicCoefficients (DiracHilbert →L[ℂ] DiracHilbert) :=
    { constant := matrixOperator H.constant
      firstCosine := matrixOperator H.firstCosine
      firstSine := matrixOperator H.firstSine
      secondCosine := matrixOperator H.secondCosine
      secondMixed := matrixOperator H.secondMixed }
  have hVertex :
      inPlanePauliVertexOperator coefficients =
        matrixOperator (coefficients 0 • sigmaX + coefficients 1 • sigmaY) := by
    simp [inPlanePauliVertexOperator, matrixOperator, map_add, map_smul]
  have hpoint (θ : ℝ) :
      polarPauliOperator aR bR dR θ *
          inPlanePauliVertexOperator coefficients *
          polarPauliOperator aA bA dA θ = HO.eval θ := by
    rw [hVertex]
    unfold polarPauliOperator
    change
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ]
          (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aR bR dR θ) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ]
          (DiracHilbert →L[ℂ] DiracHilbert))
          (coefficients 0 • sigmaX + coefficients 1 • sigmaY) *
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ]
          (DiracHilbert →L[ℂ] DiracHilbert))
          (polarPauliMatrix aA bA dA θ) = _
    rw [← map_mul, ← map_mul,
      show polarPauliMatrix aR bR dR θ *
          (coefficients 0 • sigmaX + coefficients 1 • sigmaY) *
          polarPauliMatrix aA bA dA θ = H.eval θ from
        polarPauliMatrix_inPlane_sandwich_eq_harmonics
          aR bR dR aA bA dA coefficients θ]
    dsimp only [HO, AngularHarmonicCoefficients.eval, matrixOperator]
    simp only [map_add, map_smul]
  change
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarPauliOperator aR bR dR θ *
        inPlanePauliVertexOperator coefficients *
        polarPauliOperator aA bA dA θ) = _
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarPauliOperator aR bR dR θ *
        inPlanePauliVertexOperator coefficients *
        polarPauliOperator aA bA dA θ) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), HO.eval θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact hpoint θ
    _ = (2 * Real.pi : ℝ) • HO.constant := HO.integral_eval
    _ = inPlanePauliVertexOperator
        (inPlaneLadderAction
          (pauliRungAngularCoefficient aR aA dR dA) coefficients) := by
      have hvertexAction :
          inPlanePauliVertexOperator
              (inPlaneLadderAction
                (pauliRungAngularCoefficient aR aA dR dA) coefficients) =
            matrixOperator
              ((inPlaneLadderAction
                (pauliRungAngularCoefficient aR aA dR dA) coefficients) 0 • sigmaX +
               (inPlaneLadderAction
                (pauliRungAngularCoefficient aR aA dR dA) coefficients) 1 • sigmaY) := by
        simp [inPlanePauliVertexOperator, matrixOperator, map_add, map_smul]
      rw [hvertexAction]
      change
        ((2 * Real.pi : ℝ) : ℂ) •
          (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ]
            (DiracHilbert →L[ℂ] DiracHilbert)) H.constant =
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ]
            (DiracHilbert →L[ℂ] DiracHilbert))
          ((inPlaneLadderAction
              (pauliRungAngularCoefficient aR aA dR dA) coefficients) 0 • sigmaX +
           (inPlaneLadderAction
              (pauliRungAngularCoefficient aR aA dR dA) coefficients) 1 • sigmaY)
      rw [← map_smul]
      apply congrArg (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ]
        (DiracHilbert →L[ℂ] DiracHilbert))
      simp only [H, polarPauliInPlaneHarmonics, pauliRungAngularCoefficient,
        inPlaneLadderAction_apply_x, inPlaneLadderAction_apply_y,
        smul_add, smul_sub, smul_smul]
      module

end

end QuantumTheory.Models.MassiveDirac
