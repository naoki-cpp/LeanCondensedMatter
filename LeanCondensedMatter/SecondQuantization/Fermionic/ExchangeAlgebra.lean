import LeanCondensedMatter.SecondQuantization.Fermionic.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Common.ExchangeAlgebra

set_option linter.style.header false

/-!
# The fermionic `Common.ExchangeAlgebra` instance

Instantiates `Common/ExchangeAlgebra.lean`'s `Common.ExchangeAlgebra` at `Statistics.fermion` for
`FermionOccupation Mode`, from `CanonicalAnticommutationRelations.lean`'s CAR facts
(`anticomm_annihilate_create`/`_annihilate_annihilate`/`_create_create`) via the bridging fact
that `Common.exchangeCommutator Statistics.fermion` and `anticomm` are the same operator, for
*any* two operators (not just at a single mode — unlike `Fermionic/NumberOperator.lean`'s
`exchangeCommutator_annihilate_create_self`, which only needed this at `i = j`, a general Wick
induction needs the all-index exchange relation this instance packages).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

omit [LinearOrder Mode] in
/-- **`Common.exchangeCommutator Statistics.fermion = anticomm`**: CAR's anticommutator is exactly
the `ζ = -1` case of the `ζ`-commutator (`Common.zetaCommutator`), for arbitrary operators `A`, `B`
(not just at a single mode). -/
theorem exchangeCommutator_fermion_eq_anticomm
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    Common.exchangeCommutator Statistics.fermion A B = anticomm A B := by
  rw [Common.exchangeCommutator, Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one,
    Common.zetaCommutator, neg_one_smul, sub_neg_eq_add]
  rfl

/-- **The fermionic exchange algebra.** -/
noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Statistics.fermion Mode (FermionOccupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    rw [exchangeCommutator_fermion_eq_anticomm, anticomm_annihilate_create]
  annihilate_annihilate i j := by
    rw [exchangeCommutator_fermion_eq_anticomm, anticomm_annihilate_annihilate]
  create_create i j := by
    rw [exchangeCommutator_fermion_eq_anticomm, anticomm_create_create]

end SecondQuantization
