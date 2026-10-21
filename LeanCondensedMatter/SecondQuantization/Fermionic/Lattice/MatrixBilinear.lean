import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option linter.style.header false

/-! # Finite fermionic matrix bilinears

The matrix coefficient `M i j` multiplies `c†(label i)c(label j)` on the full finite
Fock space. The construction is linear and preserves adjoints; it is not multiplicative.
-/

namespace SecondQuantization.Fermionic.Lattice

open scoped BigOperators

noncomputable section

variable {Index Mode : Type*} [Fintype Index] [Fintype Mode] [LinearOrder Mode]

/-- The creation-annihilation bilinear associated with a matrix and a choice of modes. -/
def matrixBilinear (label : Index → Mode) :
    Matrix Index Index ℂ →ₗ[ℂ]
      (FiniteLatticeHilbertFock Mode →L[ℂ] FiniteLatticeHilbertFock Mode) where
  toFun M := ∑ i, ∑ j, M i j • boundedDgammaMatrixUnit (label i) (label j)
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z M := by simp [smul_smul, Finset.smul_sum]

/-- Matrix adjoints become Hilbert-space adjoints of the corresponding bilinears. -/
theorem star_matrixBilinear (label : Index → Mode) (M : Matrix Index Index ℂ) :
    star (matrixBilinear label M) = matrixBilinear label (star M) := by
  change star (∑ i, ∑ j, M i j • boundedDgammaMatrixUnit (label i) (label j)) = _
  simp only [star_sum, star_smul, star_boundedDgammaMatrixUnit]
  rw [Finset.sum_comm]
  rfl

end
end SecondQuantization.Fermionic.Lattice
