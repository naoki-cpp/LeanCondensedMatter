import LeanCondensedMatter.Analysis.Operator.Fredholm.Diagonal
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Finite-dimensional compatibility for the diagonal Fredholm determinant

This module identifies the infinite-product definition `Fredholm.diagonalDet` with Mathlib's
ordinary determinant when the supplied diagonal presentation is finite-dimensional. The ordinary
determinant is used only in this compatibility theorem; it does not define the infinite-dimensional
quantity.
-/

noncomputable section

namespace Fredholm

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a finite Hilbert basis, the diagonal Fredholm determinant agrees with Mathlib's ordinary
determinant of `1 + diagonalOp b coeff`. -/
theorem diagonalDet_eq_det_one_add_diagonalOp [Fintype ι]
    (b : HilbertBasis ι ℂ H) (coeff : ι → ℂ) :
    diagonalDet coeff =
      ((1 : H →L[ℂ] H) + HilbertBasis.diagonalOp b coeff).det := by
  classical
  let B : Basis ι ℂ H := b.toOrthonormalBasis.toBasis
  have hcoeff : Summable fun i => ‖coeff i‖ := summable_fintype _
  rw [diagonalDet_fintype]
  change (∏ i, (1 + coeff i)) =
    LinearMap.det
      (((1 : H →L[ℂ] H) + HilbertBasis.diagonalOp b coeff) : H →ₗ[ℂ] H)
  rw [← LinearMap.det_toMatrix B]
  have hmatrix :
      LinearMap.toMatrix B B
          (((1 : H →L[ℂ] H) + HilbertBasis.diagonalOp b coeff) : H →ₗ[ℂ] H) =
        Matrix.diagonal (fun i => 1 + coeff i) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [B, HilbertBasis.one_add_diagonalOp_apply_basis, hcoeff, Matrix.diagonal_apply]
  rw [hmatrix, Matrix.det_diagonal]

end Fredholm
