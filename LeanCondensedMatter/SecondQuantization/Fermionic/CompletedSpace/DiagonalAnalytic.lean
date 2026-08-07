import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option linter.style.header false

/-!
# Analytic properties of completed fermionic diagonal operators

This file develops analytic properties of the maximal weighted diagonal operators defined in
`Diagonal.lean`. The definition layer stays independent of adjoints and closed-operator theory;
this file begins that later analytic layer.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- Every maximal weighted diagonal domain contains the dense finite-support algebraic core. -/
theorem completedDiagonalDomain_dense (w : Occupation Mode → ℂ) :
    Dense ((completedDiagonalDomain w : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  apply Dense.mono ?_ algebraicToCompleted_denseRange
  rintro _ ⟨x, rfl⟩
  exact algebraicToCompleted_mem_completedDiagonalDomain w x

/-- The `LinearPMap` diagonal operator is densely defined for every weight. -/
theorem completedDiagonalOperator_denseDomain (w : Occupation Mode → ℂ) :
    Dense (((completedDiagonalOperator w).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  exact completedDiagonalDomain_dense w

/-- A diagonal operator whose weights are fixed by complex conjugation is formally symmetric. -/
theorem completedDiagonalOperator_isFormalAdjoint_self (w : Occupation Mode → ℂ)
    (hw : ∀ n, star (w n) = w n) :
    (completedDiagonalOperator w).IsFormalAdjoint (completedDiagonalOperator w) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [completedDiagonalOperator_apply, completedDiagonalOperator_apply]
  simp [RCLike.inner_apply', hw, mul_assoc, mul_left_comm, mul_comm]

/-- A formally symmetric maximal diagonal operator is closable. -/
theorem completedDiagonalOperator_isClosable_of_star (w : Occupation Mode → ℂ)
    (hw : ∀ n, star (w n) = w n) :
    (completedDiagonalOperator w).IsClosable := by
  have hdense := completedDiagonalOperator_denseDomain w
  have hsymm := completedDiagonalOperator_isFormalAdjoint_self w hw
  have hle : completedDiagonalOperator w ≤ (completedDiagonalOperator w).adjoint :=
    hsymm.le_adjoint hdense
  exact ((completedDiagonalOperator w).adjoint_isClosed hdense).isClosable.leIsClosable hle

/-- Free-Hamiltonian occupation energies are fixed by complex conjugation. -/
theorem star_freeHamiltonianWeight (ε : Mode → ℝ) (n : Occupation Mode) :
    star (freeHamiltonianWeight ε n) = freeHamiltonianWeight ε n := by
  simp [freeHamiltonianWeight]

/-- The completed free Hamiltonian is densely defined. -/
theorem completedFreeHamiltonian_denseDomain (ε : Mode → ℝ) :
    Dense (((completedFreeHamiltonian ε).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  exact completedDiagonalOperator_denseDomain (freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is formally symmetric. -/
theorem completedFreeHamiltonian_isFormalAdjoint_self (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsFormalAdjoint (completedFreeHamiltonian ε) := by
  exact completedDiagonalOperator_isFormalAdjoint_self (freeHamiltonianWeight ε)
    (star_freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is closable. -/
theorem completedFreeHamiltonian_isClosable (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsClosable := by
  exact completedDiagonalOperator_isClosable_of_star (freeHamiltonianWeight ε)
    (star_freeHamiltonianWeight ε)

/-- Total-particle-number weights are fixed by complex conjugation. -/
theorem star_particleNumberWeight (n : Occupation Mode) :
    star (particleNumber n : ℂ) = (particleNumber n : ℂ) := by
  simp

/-- The completed total number operator is densely defined. -/
theorem completedTotalNumberOperator_denseDomain :
    Dense ((completedTotalNumberOperator.domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  exact completedDiagonalOperator_denseDomain
    (fun n : Occupation Mode => (particleNumber n : ℂ))

/-- The completed total number operator is formally symmetric. -/
theorem completedTotalNumberOperator_isFormalAdjoint_self :
    completedTotalNumberOperator.IsFormalAdjoint completedTotalNumberOperator := by
  exact completedDiagonalOperator_isFormalAdjoint_self
    (fun n : Occupation Mode => (particleNumber n : ℂ)) star_particleNumberWeight

/-- The completed total number operator is closable. -/
theorem completedTotalNumberOperator_isClosable :
    completedTotalNumberOperator.IsClosable := by
  exact completedDiagonalOperator_isClosable_of_star
    (fun n : Occupation Mode => (particleNumber n : ℂ)) star_particleNumberWeight

end
end Fermionic
end SecondQuantization
