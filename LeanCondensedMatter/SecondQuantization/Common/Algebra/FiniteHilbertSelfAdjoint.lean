import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperatorAlgebra
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Adjointness of finite-Hilbert operator transport

The canonical finite-Hilbert realization of an algebraic Fock operator is written in the
configuration basis. Its matrix in the corresponding orthonormal basis is exactly the algebraic
coordinate matrix `matrixCoeff A`. Consequently adjoints and self-adjointness of bounded
transported operators are equivalent to conjugate-transpose identities for those coefficients.

This module is model-independent representation infrastructure. In particular, hopping and current
models can establish self-adjointness by proving a coefficient identity without depending on the
thermal layer.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqFiniteHilbertSelfAdjoint : DecidableEq Config := Classical.decEq Config

private noncomputable def finiteHilbertOperatorMatrix
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    Matrix Config Config ℂ :=
  LinearMap.toMatrix
    (finiteHilbertOrthonormalBasis (Config := Config)).toBasis
    (finiteHilbertOrthonormalBasis (Config := Config)).toBasis
    (finiteHilbertOperator A).toLinearMap

@[simp] private theorem finiteHilbertOperatorMatrix_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    finiteHilbertOperatorMatrix A m n = matrixCoeff A m n := by
  unfold finiteHilbertOperatorMatrix
  rw [LinearMap.toMatrix_apply]
  change
    ((EuclideanSpace.basisFun Config ℂ).repr
      (finiteHilbertOperator A (finiteHilbertBasisState n))).ofLp m =
        matrixCoeff A m n
  rw [EuclideanSpace.basisFun_repr]
  exact finiteHilbertOperator_basis_apply A m n

/-- Adjointness after finite-Hilbert transport is exactly conjugate transposition of the algebraic
coordinate matrix. -/
theorem star_finiteHilbertOperator_eq_iff_matrixCoeff
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    star (finiteHilbertOperator A) = finiteHilbertOperator B ↔
      ∀ m n : Config, star (matrixCoeff A n m) = matrixCoeff B m n := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  let b := (finiteHilbertOrthonormalBasis (Config := Config)).toBasis
  constructor
  · intro h m n
    have hlin :
        LinearMap.adjoint (finiteHilbertOperator A).toLinearMap =
          (finiteHilbertOperator B).toLinearMap := by
      rw [ContinuousLinearMap.adjoint_toLinearMap]
      exact congrArg ContinuousLinearMap.toLinearMap h
    have hmat := congrArg (fun T => LinearMap.toMatrix b b T m n) hlin
    rw [LinearMap.toMatrix_adjoint] at hmat
    change star (finiteHilbertOperatorMatrix A n m) =
      finiteHilbertOperatorMatrix B m n at hmat
    simpa using hmat
  · intro h
    have hmat :
        LinearMap.toMatrix b b
            (LinearMap.adjoint (finiteHilbertOperator A).toLinearMap) =
          LinearMap.toMatrix b b (finiteHilbertOperator B).toLinearMap := by
      ext m n
      rw [LinearMap.toMatrix_adjoint]
      change star (finiteHilbertOperatorMatrix A n m) =
        finiteHilbertOperatorMatrix B m n
      simpa using h m n
    have hlin :
        LinearMap.adjoint (finiteHilbertOperator A).toLinearMap =
          (finiteHilbertOperator B).toLinearMap :=
      (LinearMap.toMatrix b b).injective hmat
    rw [ContinuousLinearMap.adjoint_toLinearMap] at hlin
    exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun hlin x

private theorem finiteHilbertOperator_isSelfAdjoint_iff_matrix_isHermitian
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    IsSelfAdjoint (finiteHilbertOperator A) ↔
      (finiteHilbertOperatorMatrix A).IsHermitian := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  simpa [finiteHilbertOperatorMatrix] using
    (LinearMap.isHermitian_toMatrix_iff
      (finiteHilbertOrthonormalBasis (Config := Config))).symm

/-- Coefficient-level criterion for self-adjointness after finite-Hilbert transport. -/
theorem finiteHilbertOperator_isSelfAdjoint_iff_matrixCoeff
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    IsSelfAdjoint (finiteHilbertOperator A) ↔
      ∀ m n : Config, star (matrixCoeff A n m) = matrixCoeff A m n := by
  rw [finiteHilbertOperator_isSelfAdjoint_iff_matrix_isHermitian]
  rw [Matrix.IsHermitian.ext_iff]
  simp only [finiteHilbertOperatorMatrix_apply]

end
end Common
end SecondQuantization
