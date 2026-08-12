import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# The fermionic `Common.ExchangeAlgebra` instance

Instantiates `Common/Algebra/ExchangeAlgebra.lean`'s `Common.ExchangeAlgebra` at `Common.Statistics.fermion` for
`Occupation Mode`, from `CanonicalAnticommutationRelations.lean`'s CAR facts
(`anticomm_annihilate_create`/`_annihilate_annihilate`/`_create_create`) via the bridging fact
that `Common.exchangeCommutator Common.Statistics.fermion` and `anticomm` are the same operator, for
*any* two operators (not just at a single mode — unlike `Fermionic/Algebra/NumberOperator.lean`'s
`exchangeCommutator_annihilate_create_self`, which only needed this at `i = j`, a general Wick
induction needs the all-index exchange relation this instance packages).
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

omit [LinearOrder Mode] in
/-- **`Common.exchangeCommutator Common.Statistics.fermion = anticomm`**: CAR's anticommutator is exactly
the `ζ = -1` case of the `ζ`-commutator (`Common.zetaCommutator`), for arbitrary operators `A`, `B`
(not just at a single mode). -/
theorem exchangeCommutator_fermion_eq_anticomm
    (A B : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.exchangeCommutator Common.Statistics.fermion A B = anticomm A B := by
  rw [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one,
    Common.zetaCommutator, neg_one_smul, sub_neg_eq_add]
  rfl

/-- **The fermionic exchange algebra.** -/
noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Common.Statistics.fermion Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    rw [exchangeCommutator_fermion_eq_anticomm, anticomm_annihilate_create]
  annihilate_annihilate i j := by
    rw [exchangeCommutator_fermion_eq_anticomm, anticomm_annihilate_annihilate]
  create_create i j := by
    rw [exchangeCommutator_fermion_eq_anticomm, anticomm_create_create]

end Fermionic
end SecondQuantization
