import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Bosonic diagonal operators on completed Fock space

The single-mode number operator and free Hamiltonian are unbounded on completed bosonic Fock space.
They are therefore realized as maximal diagonal `LinearPMap` operators on their natural weighted
`ℓ²` domains, using the statistics-independent completed diagonal infrastructure.

The finite-support algebraic Fock space lies in both domains, and the completed operators agree
there with the existing algebraic bosonic number operator and free Hamiltonian.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- Natural weighted `ℓ²` domain of the single-mode bosonic number operator. -/
noncomputable def completedNumberOperatorDomain (i : Mode) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  Common.completedDiagonalDomain fun n : Occupation Mode => (n i : ℂ)

/-- Single-mode bosonic number operator on completed Fock space. -/
noncomputable def completedNumberOperator (i : Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  Common.completedDiagonalOperator fun n : Occupation Mode => (n i : ℂ)

/-- Natural weighted `ℓ²` domain of the completed free bosonic Hamiltonian. -/
noncomputable def completedFreeHamiltonianDomain (ε : Mode → ℝ) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  Common.completedDiagonalDomain fun n : Occupation Mode => (freeEigenvalue ε n : ℂ)

/-- Free bosonic Hamiltonian on completed Fock space. -/
noncomputable def completedFreeHamiltonian (ε : Mode → ℝ) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  Common.completedDiagonalOperator fun n : Occupation Mode => (freeEigenvalue ε n : ℂ)

/-- Every occupation-basis vector lies in the completed single-mode number-operator domain. -/
theorem completedBasisState_mem_completedNumberOperatorDomain (i : Mode) (n : Occupation Mode) :
    completedBasisState n ∈ completedNumberOperatorDomain i := by
  exact Common.completedBasisState_mem_completedDiagonalDomain
    (fun m : Occupation Mode => (m i : ℂ)) n

/-- Occupation-basis vectors diagonalize the completed single-mode number operator. -/
@[simp]
theorem completedNumberOperator_basisState (i : Mode) (n : Occupation Mode) :
    completedNumberOperator i
        ⟨completedBasisState n, completedBasisState_mem_completedNumberOperatorDomain i n⟩ =
      (n i : ℂ) • completedBasisState n := by
  exact Common.completedDiagonalOperator_basisState
    (fun m : Occupation Mode => (m i : ℂ)) n

/-- Every occupation-basis vector lies in the completed free-Hamiltonian domain. -/
theorem completedBasisState_mem_completedFreeHamiltonianDomain
    (ε : Mode → ℝ) (n : Occupation Mode) :
    completedBasisState n ∈ completedFreeHamiltonianDomain ε := by
  exact Common.completedBasisState_mem_completedDiagonalDomain
    (fun m : Occupation Mode => (freeEigenvalue ε m : ℂ)) n

/-- Occupation-basis vectors diagonalize the completed free Hamiltonian. -/
@[simp]
theorem completedFreeHamiltonian_basisState (ε : Mode → ℝ) (n : Occupation Mode) :
    completedFreeHamiltonian ε
        ⟨completedBasisState n, completedBasisState_mem_completedFreeHamiltonianDomain ε n⟩ =
      (freeEigenvalue ε n : ℂ) • completedBasisState n := by
  exact Common.completedDiagonalOperator_basisState
    (fun m : Occupation Mode => (freeEigenvalue ε m : ℂ)) n

/-- On the finite-support core, the completed single-mode number operator agrees with the algebraic
operator `aᵢ† aᵢ`. -/
theorem completedNumberOperator_comp_algebraicCore (i : Mode) :
    (completedNumberOperator i).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (n i : ℂ))) =
      algebraicToCompleted.comp (numberOperator i) := by
  rw [numberOperator_eq_diagonalOperator]
  simpa [completedNumberOperator, algebraicToCompleted] using
    (Common.completedDiagonalOperator_comp_algebraicCore
      (fun n : Occupation Mode => (n i : ℂ)))

/-- On the finite-support core, the completed free Hamiltonian agrees with the existing algebraic
free bosonic Hamiltonian. -/
theorem completedFreeHamiltonian_comp_algebraicCore (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (freeEigenvalue ε n : ℂ))) =
      algebraicToCompleted.comp (freeHamiltonian ε) := by
  simpa [completedFreeHamiltonian, algebraicToCompleted, freeHamiltonian] using
    (Common.completedDiagonalOperator_comp_algebraicCore
      (fun n : Occupation Mode => (freeEigenvalue ε n : ℂ)))

end
end Bosonic
end SecondQuantization
