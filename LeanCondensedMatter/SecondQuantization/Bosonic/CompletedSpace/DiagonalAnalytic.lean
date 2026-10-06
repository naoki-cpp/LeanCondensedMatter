import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic

set_option linter.style.header false

/-!
# Analytic properties of completed bosonic diagonal operators

Dense domain, closedness, and exact adjoint formulas are supplied by the generic maximal diagonal
operator theory in `Common.CompletedSpace.DiagonalAnalytic`. This file keeps only the named bosonic
self-adjointness endpoints for the single-mode number operator and free Hamiltonian.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- The completed single-mode bosonic number operator is self-adjoint. -/
theorem completedNumberOperator_isSelfAdjoint (i : Mode) :
    IsSelfAdjoint (completedNumberOperator i) := by
  exact Common.completedDiagonalOperator_isSelfAdjoint_of_star
    (fun n : Occupation Mode => (n i : ℂ))
    (fun n => by simp)

/-- The completed free bosonic Hamiltonian is self-adjoint for arbitrary real one-particle
energies. -/
theorem completedFreeHamiltonian_isSelfAdjoint (ε : Mode → ℝ) :
    IsSelfAdjoint (completedFreeHamiltonian ε) := by
  exact Common.completedDiagonalOperator_isSelfAdjoint_of_star
    (fun n : Occupation Mode => (freeEigenvalue ε n : ℂ))
    (fun n => by simp)

end
end Bosonic
end SecondQuantization
