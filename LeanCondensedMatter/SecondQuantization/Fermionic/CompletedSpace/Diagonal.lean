import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Fermionic diagonal operators on completed Fock space

The statistics-independent maximal weighted `ℓ²` diagonal operator is owned by
`Common.CompletedSpace.Diagonal`. This file keeps the fermionic free-Hamiltonian and total-number
weights together with their algebraic-core compatibility endpoints.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- Occupation energy used by the free Hamiltonian. -/
noncomputable def freeHamiltonianWeight (ε : Mode → ℝ) (n : Occupation Mode) : ℂ :=
  ∑ i ∈ n, (ε i : ℂ)

/-- Natural weighted `ℓ²` domain of the free Hamiltonian. -/
noncomputable def completedFreeHamiltonianDomain (ε : Mode → ℝ) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  Common.completedDiagonalDomain (freeHamiltonianWeight ε)

/-- Free Hamiltonian on completed Fock space, with its natural weighted square-summability domain. -/
noncomputable def completedFreeHamiltonian (ε : Mode → ℝ) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  Common.completedDiagonalOperator (freeHamiltonianWeight ε)

/-- Natural domain of the total number operator on the completed Fock space. -/
noncomputable def completedTotalNumberDomain :
    Submodule ℂ (CompletedFockSpace Mode) :=
  Common.completedDiagonalDomain fun n : Occupation Mode => (particleNumber n : ℂ)

/-- Total particle-number operator as an unbounded diagonal partial linear map. -/
noncomputable def completedTotalNumberOperator :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  Common.completedDiagonalOperator fun n : Occupation Mode => (particleNumber n : ℂ)

/-- The completed free Hamiltonian extends the algebraic free Hamiltonian on the entire
finite-support core. -/
theorem completedFreeHamiltonian_comp_algebraicCore (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain (freeHamiltonianWeight ε)) =
      algebraicToCompleted.comp (freeHamiltonian ε) := by
  change
    (Common.completedDiagonalOperator (freeHamiltonianWeight ε)).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain (freeHamiltonianWeight ε)) =
      Common.algebraicToCompleted.comp
        (Common.diagonalOperator (freeHamiltonianWeight ε))
  exact Common.completedDiagonalOperator_comp_algebraicCore (freeHamiltonianWeight ε)

/-- The completed total-number operator extends the algebraic total-number operator on the entire
finite-support core. -/
theorem completedTotalNumberOperator_comp_algebraicCore :
    completedTotalNumberOperator.toFun.comp
        (Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (particleNumber n : ℂ))) =
      algebraicToCompleted.comp
        (totalNumberOperator : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  change
    (Common.completedDiagonalOperator
      (fun n : Occupation Mode => (particleNumber n : ℂ))).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (particleNumber n : ℂ))) =
      Common.algebraicToCompleted.comp
        (Common.diagonalOperator fun n : Occupation Mode => (particleNumber n : ℂ))
  exact Common.completedDiagonalOperator_comp_algebraicCore
    (fun n : Occupation Mode => (particleNumber n : ℂ))

end
end Fermionic
end SecondQuantization
