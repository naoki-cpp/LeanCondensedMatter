import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Bosonic.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Common.ExchangeCommutator

set_option linter.style.header false

/-!
# The bosonic number operator, and the reordering identity `a_i a_i† = id + N_i`

The bosonic counterpart of `Fermionic/Hamiltonian.lean`'s `numberOperator`/`numberOperator_apply`/
`numberOperator_basisState`, and of `Fermionic/FreeTwoPointFunction.lean`'s
`annihilate_comp_create_self`. Unlike the fermionic line, no Hamiltonian is built from
`numberOperator` yet — this file only introduces `Nᵢ := aᵢ†aᵢ` itself, needed to state
`annihilate_comp_create_self` below.

`annihilate_comp_create_self` is proved as an instance of `Common.ExchangeCommutator`'s unified
reordering identity (`Common.comp_eq_id_add_of_zetaCommutator_eq_id`), for the bosonic statistics
(`Statistics.zetaInt Statistics.boson = 1`), mirroring the fermionic proof exactly — see
`Common/ExchangeCommutator.lean`'s module docstring for why this is the same algebraic fact in
both statistics, with only the sign of `ζ` differing.
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

/-- **`[a_i, a_i†]_ζ = id`, the bosonic case (`ζ = Statistics.zetaInt Statistics.boson`)**: an
instance of `Common.exchangeCommutator_annihilate_create_self`, via the bosonic
`Common.ExchangeAlgebra` instance (`Bosonic/ExchangeAlgebra.lean`), whose `annihilate`/`create`
fields are literally `Bosonic.annihilate`/`create`. -/
theorem exchangeCommutator_annihilate_create_self (i : Mode) :
    Common.exchangeCommutator Statistics.boson (annihilate i) (create i) =
      (LinearMap.id : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :=
  Common.exchangeCommutator_annihilate_create_self (Config := Occupation Mode) i

/-- **`a_i a_i† = id + N_i`**, an instance of `Common.annihilate_comp_create_self`. The bosonic
mirror of `Fermionic/FreeTwoPointFunction.lean`'s `annihilate_comp_create_self` (`c_i c_i† = id -
N_i`), differing only in the sign of `ζ`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) =
      (LinearMap.id : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) + numberOperator i := by
  have h := Common.annihilate_comp_create_self (s := Statistics.boson) (Config := Occupation Mode)
    i
  rwa [Statistics.zetaInt_boson, Int.cast_one, one_smul] at h

end Bosonic
end SecondQuantization
