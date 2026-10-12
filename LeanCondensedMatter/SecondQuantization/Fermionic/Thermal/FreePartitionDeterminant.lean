import LeanCondensedMatter.QuantumTheory.Gibbs.FreeBoltzmannKernel
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-fermion partition function as a determinant

The finite-mode free-fermion partition function equals the determinant of one plus the diagonal
one-particle Boltzmann kernel. This is an occupation-space partition-function result.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- The finite free-fermion partition function is the determinant of `1 + K`, where `K` is the
shared diagonal one-particle Boltzmann kernel. Determinant appears only at this physical consumer
boundary; it is not a second exchange-statistics backend. -/
theorem freePartitionFunction_eq_det_one_add_freeBoltzmannModeKernel
    [LinearOrder Mode] [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β =
      Matrix.det (1 + QuantumTheory.freeBoltzmannModeKernel ε β) := by
  classical
  rw [freePartitionFunction_eq_prod]
  have hdiag :
      (1 + QuantumTheory.freeBoltzmannModeKernel ε β : Matrix Mode Mode ℂ) =
        Matrix.diagonal (fun i => 1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
    rw [QuantumTheory.freeBoltzmannModeKernel_eq_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag, Matrix.det_diagonal]

end Fermionic
end SecondQuantization
