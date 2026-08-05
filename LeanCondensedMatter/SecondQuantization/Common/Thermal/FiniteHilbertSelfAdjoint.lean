import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperatorAlgebra
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Self-adjointness of finite-Hilbert operator transport

The canonical finite-Hilbert realization of an algebraic Fock operator is written in the
configuration basis.  Its matrix in the corresponding orthonormal basis is exactly the algebraic
coordinate matrix `matrixCoeff A`.  Consequently self-adjointness of the bounded transported
operator is equivalent to the usual Hermitian symmetry of those coefficients.

This module is model-independent.  In particular, hopping and current models can establish
self-adjointness by proving a coefficient identity before entering the analytic Kubo layer.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config] [DecidableEq Config]

/-- Matrix of an algebraic Fock endomorphism in the canonical finite-Hilbert occupation basis. -/
noncomputable def finiteHilbertOperatorMatrix
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    Matrix Config Config ℂ :=
  LinearMap.toMatrix
    (finiteHilbertOrthonormalBasis (Config := Config)).toBasis
    (finiteHilbertOrthonormalBasis (Config := Config)).toBasis
    (finiteHilbertOperator A).toLinearMap

/-- The analytic matrix of the transported operator is its algebraic coordinate matrix. -/
@[simp]
theorem finiteHilbertOperatorMatrix_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    finiteHilbertOperatorMatrix A m n = matrixCoeff A m n := by
  simp [finiteHilbertOperatorMatrix, LinearMap.toMatrix_apply,
    finiteHilbertOrthonormalBasis_apply, finiteHilbertOperator_basis_apply]

/-- The transported bounded operator is self-adjoint exactly when its canonical matrix is
Hermitian. -/
theorem finiteHilbertOperator_isSelfAdjoint_iff_matrix_isHermitian
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
