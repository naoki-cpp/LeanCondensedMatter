import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Lossless diagonal expectations

For a self-adjoint operator, a diagonal matrix element is a real scalar. This module packages that
fact before transporting the scalar to `ℝ`, so propositions and implementations do not silently
discard an imaginary part with `.re`.
-/

noncomputable section

namespace ContinuousLinearMap

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal matrix element of a self-adjoint operator, bundled with its self-adjointness as a
complex scalar. -/
noncomputable def diagonalExpectationSelfAdjoint
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) : selfAdjoint ℂ :=
  ⟨inner ℂ (T x) x, by
    change IsSelfAdjoint (inner ℂ (T x) x)
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

/-- A positive operator has a nonnegative lossless diagonal expectation. -/
theorem diagonalExpectationValue_nonneg
    (T : H →L[ℂ] H) (hT : T.IsPositive) (x : H) :
    0 ≤ diagonalExpectationValue T hT.isSelfAdjoint x := by
  have hcomplex : (0 : ℂ) ≤ inner ℂ x (T x) := hT.inner_nonneg_right x
  rw [← coe_diagonalExpectationValue_right T hT.isSelfAdjoint x] at hcomplex
  exact_mod_cast hcomplex

/-- The diagonal expectation of a positive operator, with nonnegativity carried in the codomain. -/
noncomputable def diagonalExpectationNNReal
    (T : H →L[ℂ] H) (hT : T.IsPositive) (x : H) : NNReal :=
  ⟨diagonalExpectationValue T hT.isSelfAdjoint x,
    diagonalExpectationValue_nonneg T hT x⟩

@[simp]
theorem coe_diagonalExpectationNNReal
    (T : H →L[ℂ] H) (hT : T.IsPositive) (x : H) :
    (diagonalExpectationNNReal T hT x : ℝ) =
      diagonalExpectationValue T hT.isSelfAdjoint x :=
  rfl

/-- Coercing a positive diagonal expectation back to `ℂ` recovers the original matrix element. -/
theorem coe_coe_diagonalExpectationNNReal
    (T : H →L[ℂ] H) (hT : T.IsPositive) (x : H) :
    ((diagonalExpectationNNReal T hT x : ℝ) : ℂ) = inner ℂ x (T x) := by
  rw [coe_diagonalExpectationNNReal, coe_diagonalExpectationValue_right]

/-- Lossless diagonal expectation is additive in the operator. -/
@[simp]
theorem diagonalExpectationValue_add
    (T S : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hS : IsSelfAdjoint S) (x : H) :
    diagonalExpectationValue (T + S) (hT.add hS) x =
      diagonalExpectationValue T hT x + diagonalExpectationValue S hS x := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right, Complex.ofReal_add,
    coe_diagonalExpectationValue_right, coe_diagonalExpectationValue_right]
  simp [inner_add_right]

/-- Equal diagonal matrix elements give equal lossless diagonal-expectation values. -/
theorem diagonalExpectationValue_eq_of_inner_eq
    {T S : H →L[ℂ] H} (hT : IsSelfAdjoint T) (hS : IsSelfAdjoint S) (x : H)
    (h : inner ℂ x (T x) = inner ℂ x (S x)) :
    diagonalExpectationValue T hT x = diagonalExpectationValue S hS x := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right, coe_diagonalExpectationValue_right, h]


/-- In finite dimension, the lossless diagonal expectation of a self-adjoint operator is the
weighted sum of the eigenvalues in any supplied orthonormal eigenbasis, with squared basis
coordinates as weights. -/
theorem diagonalExpectationValue_eq_sum_orthonormal_eigenbasis
    {ι : Type*} [Fintype ι] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (b : OrthonormalBasis ι ℂ H) (E : ι → ℝ)
    (hE : ∀ i, (T : H →ₗ[ℂ] H) (b i) = (E i : ℂ) • b i) (x : H) :
    diagonalExpectationValue T hT x =
      ∑ i, E i * ‖b.repr x i‖ ^ 2 := by
  have hcoord (i : ι) : b.repr (T x) i = (E i : ℂ) * b.repr x i := by
    calc
      b.repr (T x) i = inner ℂ (b i) (T x) := b.repr_apply_apply (T x) i
      _ = inner ℂ (T (b i)) x := (hT.isSymmetric (b i) x).symm
      _ = inner ℂ ((E i : ℂ) • b i) x := by
        apply congrArg (fun y : H => inner ℂ y x)
        exact hE i
      _ = (E i : ℂ) * inner ℂ (b i) x := by
        rw [inner_smul_left]
        simp
      _ = (E i : ℂ) * b.repr x i := by rw [b.repr_apply_apply]
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue]
  have hinner := b.repr.inner_map_map (T x) x
  rw [PiLp.inner_apply] at hinner
  rw [← hinner]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord i]
  change
    inner ℂ ((E i : ℂ) * b.repr x i) (b.repr x i) =
      (E i : ℂ) * (‖b.repr x i‖ : ℂ) ^ 2
  rw [show (E i : ℂ) * b.repr x i = (E i : ℂ) • b.repr x i from rfl]
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp

end ContinuousLinearMap
