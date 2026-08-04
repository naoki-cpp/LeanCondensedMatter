import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Lossless diagonal expectations

For a self-adjoint operator, a diagonal matrix element is a real scalar. This module packages that
fact before transporting the scalar to `ℝ`, so public propositions do not silently discard an
imaginary part with `.re`.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal matrix element of a self-adjoint operator, bundled with its self-adjointness as a
complex scalar. -/
noncomputable def diagonalExpectationSelfAdjoint
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) : selfAdjoint ℂ :=
  ⟨inner ℂ (T x) x, by
    show IsSelfAdjoint (inner ℂ (T x) x)
    have hsym : (T : H →ₗ[ℂ] H).IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
    exact ((LinearMap.isSymmetric_iff_inner_map_self_real (T : H →ₗ[ℂ] H)).mp hsym x)⟩

/-- The real value of a self-adjoint diagonal matrix element, obtained losslessly through
`Complex.selfAdjointEquiv`. -/
noncomputable def diagonalExpectationValue
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) : ℝ :=
  Complex.selfAdjointEquiv (diagonalExpectationSelfAdjoint T hT x)

/-- Transporting a self-adjoint diagonal expectation to `ℝ` and back to `ℂ` recovers the original
matrix element exactly. -/
@[simp]
theorem coe_diagonalExpectationValue
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    (diagonalExpectationValue T hT x : ℂ) = inner ℂ (T x) x := by
  have hsym : (T : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  apply Complex.ext
  · rfl
  · simpa [diagonalExpectationValue, diagonalExpectationSelfAdjoint,
      Complex.selfAdjointEquiv] using (hsym.im_inner_apply_self x).symm

/-- The same lossless coercion identity in the physicists' inner-product orientation. -/
@[simp]
theorem coe_diagonalExpectationValue_right
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    (diagonalExpectationValue T hT x : ℂ) = inner ℂ x (T x) := by
  have hsym : (T : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  calc
    (diagonalExpectationValue T hT x : ℂ) = inner ℂ (T x) x :=
      coe_diagonalExpectationValue T hT x
    _ = inner ℂ x (T x) := hsym x x

end ContinuousLinearMap
