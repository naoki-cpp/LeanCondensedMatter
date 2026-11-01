import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannWeightSummable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-boson partition sum as an inverse determinant

For finitely many modes and positive `β εᵢ`, the already-convergent bosonic occupation-space
partition sum equals `det(1 - K)⁻¹`, where `K` is the `Matrix.diagonal` of one-particle
Boltzmann weights.

This is an analytic/physical consumer theorem. It is proved from the existing real-valued product
formula and does not evaluate any formal power series at `t = 1`.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality used only by diagonal matrix and determinant plumbing. -/
local instance instDecidableEqFreePartitionDeterminant : DecidableEq Mode := Classical.decEq Mode

/-- The convergent finite-mode free-boson partition sum is the inverse determinant of
`1 - K`, with `K` the diagonal matrix of one-particle Boltzmann weights. -/
theorem tsum_boltzmannWeight_eq_inv_det_one_sub_diagonal_exp
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    ((∑' n, boltzmannWeight ε β n : ℝ) : ℂ) =
      (Matrix.det (1 - Matrix.diagonal
        (fun i : Mode => Complex.exp (-(β : ℂ) * (ε i : ℂ)))))⁻¹ := by
  rw [tsum_boltzmannWeight ε β hpos]
  have hdiag :
      (1 - Matrix.diagonal (fun i : Mode => Complex.exp (-(β : ℂ) * (ε i : ℂ)))
        : Matrix Mode Mode ℂ) =
        Matrix.diagonal (fun i => 1 - Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [hdiag, Matrix.det_diagonal]
  rw [Complex.ofReal_prod]
  simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_exp]
  rw [Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  push_cast
  ring

end
end Bosonic
end SecondQuantization
