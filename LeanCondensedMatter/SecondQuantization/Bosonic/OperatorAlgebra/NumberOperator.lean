import LeanCondensedMatter.SecondQuantization.Bosonic.OperatorAlgebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Bosonic number operator

The single-mode number operator is `N_i = a_i† a_i`. Its basis states have eigenvalue `n_i`, and
the exchange-algebra interface gives the reordering identity `a_i a_i† = id + N_i`.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The single-mode number operator `N_i = a_i† a_i`. -/
noncomputable def numberOperator (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (create i).comp (annihilate i)

theorem numberOperator_apply (i : Mode) (x : FockSpace Mode) :
    numberOperator i x = create i (annihilate i x) :=
  rfl

/-- The number-operator eigenvalue equation `N_i |n⟩ = n_i |n⟩`. -/
theorem numberOperator_basisState (i : Mode) (n : Occupation Mode) :
    numberOperator i (basisState n) = (n i : ℂ) • basisState n :=
  create_annihilate_basisState_same i n

/-- The single-mode bosonic exchange commutator is the identity. -/
theorem exchangeCommutator_annihilate_create_self (i : Mode) :
    Common.exchangeCommutator Statistics.boson (annihilate i) (create i) =
      (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :=
  Common.exchangeCommutator_annihilate_create_self (Config := Occupation Mode) i

/-- The reordering identity `a_i a_i† = id + N_i`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) =
      (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) + numberOperator i := by
  have h := Common.annihilate_comp_create_self (s := Statistics.boson) (Config := Occupation Mode) i
  rwa [Statistics.zetaInt_boson, Int.cast_one, one_smul] at h

end Bosonic
end SecondQuantization
