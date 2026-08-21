import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Fermionic diagonal operators on completed Fock space

The statistics-independent maximal weighted `ℓ²` diagonal operator is owned by
`Common.CompletedSpace.Diagonal`. This file keeps only the fermionic free-Hamiltonian and
total-number weights, domains, and operator specializations.
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

end
end Fermionic
end SecondQuantization
