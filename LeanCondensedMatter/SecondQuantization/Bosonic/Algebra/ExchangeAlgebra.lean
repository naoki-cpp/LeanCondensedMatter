import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CCR
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-! # Bosonic exchange-algebra instance -/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality for the bosonic exchange-algebra instance. -/
local instance instDecidableEqExchangeAlgebra : DecidableEq Mode := Classical.decEq Mode

noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Common.Statistics.boson Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_boson] using
      comm_annihilate_create i j
  annihilate_annihilate i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_boson] using
      comm_annihilate_annihilate i j
  create_create i j := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_boson] using
      comm_create_create i j

end
end Bosonic
end SecondQuantization
