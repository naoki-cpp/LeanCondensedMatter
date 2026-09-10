import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-! # Fermionic exchange-algebra instance -/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- The fermionic exchange algebra. -/
noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Common.Statistics.fermion Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion,
      LinearMap.zetaCommutator, anticomm] using anticomm_annihilate_create i j
  annihilate_annihilate i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion,
      LinearMap.zetaCommutator, anticomm] using anticomm_annihilate_annihilate i j
  create_create i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion,
      LinearMap.zetaCommutator, anticomm] using anticomm_create_create i j

end Fermionic
end SecondQuantization
