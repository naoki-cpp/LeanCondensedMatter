import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic

set_option linter.style.header false

/-!
# Analytic properties of completed fermionic diagonal operators

The statistics-independent analytic theory of maximal diagonal multiplication operators is owned by
`Common.CompletedSpace.DiagonalAnalytic`. This file keeps only the fermionic free-Hamiltonian and
total-number specializations.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- Free-Hamiltonian occupation energies are fixed by complex conjugation. -/
theorem star_freeHamiltonianWeight (ε : Mode → ℝ) (n : Occupation Mode) :
    star (freeHamiltonianWeight ε n) = freeHamiltonianWeight ε n := by
  simp [freeHamiltonianWeight]

/-- The completed free Hamiltonian is densely defined. -/
theorem completedFreeHamiltonian_denseDomain (ε : Mode → ℝ) :
    Dense (((completedFreeHamiltonian ε).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  exact Common.completedDiagonalOperator_denseDomain (freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is closed. -/
theorem completedFreeHamiltonian_isClosed (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsClosed := by
  exact Common.completedDiagonalOperator_isClosed (freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is formally symmetric. -/
theorem completedFreeHamiltonian_isFormalAdjoint_self (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsFormalAdjoint (completedFreeHamiltonian ε) := by
  exact Common.completedDiagonalOperator_isFormalAdjoint_self (freeHamiltonianWeight ε)
    (star_freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is self-adjoint. -/
theorem completedFreeHamiltonian_isSelfAdjoint (ε : Mode → ℝ) :
    IsSelfAdjoint (completedFreeHamiltonian ε) := by
  exact Common.completedDiagonalOperator_isSelfAdjoint_of_star (freeHamiltonianWeight ε)
    (star_freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is closable. -/
theorem completedFreeHamiltonian_isClosable (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsClosable :=
  (completedFreeHamiltonian_isClosed ε).isClosable

/-- Total-particle-number weights are fixed by complex conjugation. -/
theorem star_particleNumberWeight (n : Occupation Mode) :
    star (particleNumber n : ℂ) = (particleNumber n : ℂ) := by
  simp

/-- The completed total number operator is densely defined. -/
theorem completedTotalNumberOperator_denseDomain {Mode : Type*} :
    Dense (((completedTotalNumberOperator (Mode := Mode)).domain :
      Submodule ℂ (CompletedFockSpace Mode)) : Set (CompletedFockSpace Mode)) := by
  exact Common.completedDiagonalOperator_denseDomain
    (fun n : Occupation Mode => (particleNumber n : ℂ))

/-- The completed total number operator is closed. -/
theorem completedTotalNumberOperator_isClosed {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsClosed := by
  exact Common.completedDiagonalOperator_isClosed
    (fun n : Occupation Mode => (particleNumber n : ℂ))

/-- The completed total number operator is formally symmetric. -/
theorem completedTotalNumberOperator_isFormalAdjoint_self {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsFormalAdjoint
      (completedTotalNumberOperator (Mode := Mode)) := by
  exact Common.completedDiagonalOperator_isFormalAdjoint_self
    (fun n : Occupation Mode => (particleNumber n : ℂ))
    (star_particleNumberWeight (Mode := Mode))

/-- The completed total number operator is self-adjoint. -/
theorem completedTotalNumberOperator_isSelfAdjoint {Mode : Type*} :
    IsSelfAdjoint (completedTotalNumberOperator (Mode := Mode)) := by
  exact Common.completedDiagonalOperator_isSelfAdjoint_of_star
    (fun n : Occupation Mode => (particleNumber n : ℂ))
    (star_particleNumberWeight (Mode := Mode))

/-- The completed total number operator is closable. -/
theorem completedTotalNumberOperator_isClosable {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsClosable :=
  (completedTotalNumberOperator_isClosed (Mode := Mode)).isClosable

end
end Fermionic
end SecondQuantization
