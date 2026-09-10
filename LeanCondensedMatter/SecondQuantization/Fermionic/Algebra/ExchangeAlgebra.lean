import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-! # Fermionic exchange-algebra instance -/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

omit [LinearOrder Mode] in
/-- The fermionic exchange bracket is the anticommutator. -/
theorem exchangeCommutator_fermion_eq_anticomm
    (A B : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.exchangeCommutator Common.Statistics.fermion A B = anticomm A B := by
  simp [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion,
    LinearMap.zetaCommutator, anticomm]

/-- The fermionic exchange algebra. -/
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
