import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CCR
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-! # Bosonic exchange-algebra instance -/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

local instance instDecidableEqExchangeAlgebra : DecidableEq Mode := Classical.decEq Mode

/-- The bosonic exchange bracket is the ordinary commutator. -/
theorem exchangeCommutator_boson_eq_comm
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.exchangeCommutator Common.Statistics.boson A B = comm A B := by
  simp [Common.exchangeCommutator, Common.Statistics.zetaInt_boson]

noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Common.Statistics.boson Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    rw [exchangeCommutator_boson_eq_comm, comm_annihilate_create]
  annihilate_annihilate i j := by
    rw [exchangeCommutator_boson_eq_comm, comm_annihilate_annihilate]
  create_create i j := by
    rw [exchangeCommutator_boson_eq_comm, comm_create_create]

end
end Bosonic
end SecondQuantization
