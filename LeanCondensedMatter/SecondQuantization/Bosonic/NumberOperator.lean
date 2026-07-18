import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Common.GradedCommutator

set_option linter.style.header false

/-!
# The bosonic number operator, and the self-contraction identity `a_i a_i† = id + N_i`

The bosonic counterpart of `Fermionic/Hamiltonian.lean`'s `numberOperator`/`numberOperator_apply`/
`numberOperator_basisState`, and of `Fermionic/FreeTwoPointFunction.lean`'s
`annihilate_comp_create_self`. Unlike the fermionic line, no Hamiltonian is built from
`numberOperator` yet — this file only introduces `Nᵢ := aᵢ†aᵢ` itself, needed to state
`annihilate_comp_create_self` below.

`annihilate_comp_create_self` is proved as an instance of `Common.GradedCommutator`'s unified
self-contraction identity (`Common.selfContraction_of_gradedCommutator_eq_id`), at `ζ = 1`
(`Statistics.zetaInt Statistics.boson`), mirroring the fermionic proof at `ζ = -1` exactly — see
`Common/GradedCommutator.lean`'s module docstring for why this is the same algebraic fact in both
statistics, with only the sign of `ζ` differing.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **The single-mode number operator** `Nᵢ := aᵢ† aᵢ`. -/
noncomputable def numberOperator (i : Mode) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  (create i).comp (annihilate i)

theorem numberOperator_apply (i : Mode) (x : FockSpaceBosonic Mode) :
    numberOperator i x = create i (annihilate i x) :=
  rfl

/-- **The number-operator eigenvalue equation**, on basis states: `Nᵢ|n⟩ = n_i|n⟩`. -/
theorem numberOperator_basisState (i : Mode) (n : Occupation Mode) :
    numberOperator i (basisState n) = (n i : ℂ) • basisState n :=
  create_annihilate_basisState_same i n

/-- **`[a_i, a_i†]_1 = id`**: CCR's commutator `[a_i, a_i†] = id` (`comm_annihilate_create`) is
exactly the `ζ = 1` case of `Common.gradedCommutator`. -/
theorem gradedCommutator_annihilate_create_self (i : Mode) :
    Common.gradedCommutator (1 : ℂ) (annihilate i) (create i) =
      (LinearMap.id : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) := by
  rw [Common.gradedCommutator, one_smul]
  have h := comm_annihilate_create (Mode := Mode) i i
  rwa [if_pos rfl] at h

/-- **`a_i a_i† = id + N_i`**, from CCR's `[a_i, a_i†] = id`, via the unified graded-commutator
self-contraction identity. The bosonic mirror of `Fermionic/FreeTwoPointFunction.lean`'s
`annihilate_comp_create_self` (`c_i c_i† = id - N_i`), differing only in the sign of `ζ`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) =
      (LinearMap.id : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) + numberOperator i := by
  have h := Common.selfContraction_of_gradedCommutator_eq_id (1 : ℂ)
    (gradedCommutator_annihilate_create_self i)
  rwa [one_smul] at h

end Bosonic
end SecondQuantization
