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
theorem diagonalDet_eq_det_one_add_diagonalOp [Finite ι]
    (b : HilbertBasis ι ℂ H) (coeff : ι → ℂ) :
    diagonalDet coeff =
      ((1 : H →L[ℂ] H) + HilbertBasis.diagonalOp b coeff).det := by
  classical
  letI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ H := b.toOrthonormalBasis.toBasis
  have hB (i : ι) : B i = b i := by
    simp [B]
  have hcoeff : Summable fun i => ‖coeff i‖ := Summable.of_finite
  have happly (j : ι) :
      ((↑(1 : H →L[ℂ] H) +
          ↑(HilbertBasis.diagonalOp b coeff) : H →ₗ[ℂ] H) (B j)) =
        (1 + coeff j) • B j := by
    rw [hB j]
    change b j + HilbertBasis.diagonalOp b coeff (b j) = _
    rw [HilbertBasis.diagonalOp_apply_basis b coeff hcoeff j]
    simp [add_smul]
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
    rw [LinearMap.toMatrix_apply, happly j]
    by_cases hij : i = j
    · subst i
      simp
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  rw [hmatrix, Matrix.det_diagonal]

end Fredholm
