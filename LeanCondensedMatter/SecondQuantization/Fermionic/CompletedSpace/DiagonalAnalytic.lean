import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic

set_option linter.style.header false

/-!
# Analytic properties of completed fermionic diagonal operators

The statistics-independent analytic theory of maximal diagonal multiplication operators is owned by
`Common.CompletedSpace.DiagonalAnalytic`. This file keeps the fermionic free-Hamiltonian and
total-number self-adjointness endpoints.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- The completed free Hamiltonian is self-adjoint. -/
theorem completedFreeHamiltonian_isSelfAdjoint (ε : Mode → ℝ) :
    IsSelfAdjoint (completedFreeHamiltonian ε) := by
  exact Common.completedDiagonalOperator_isSelfAdjoint_of_star (freeHamiltonianWeight ε)
    (fun n => by simp [freeHamiltonianWeight])

/-- The completed total number operator is self-adjoint. -/
theorem completedTotalNumberOperator_isSelfAdjoint {Mode : Type*} :
    IsSelfAdjoint (completedTotalNumberOperator (Mode := Mode)) := by
  exact Common.completedDiagonalOperator_isSelfAdjoint_of_star
    (fun n : Occupation Mode => (particleNumber n : ℂ))
    (fun n => by simp)

end
end Fermionic
end SecondQuantization
