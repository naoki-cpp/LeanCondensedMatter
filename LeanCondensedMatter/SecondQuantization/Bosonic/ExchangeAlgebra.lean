import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Common.ExchangeAlgebra

set_option linter.style.header false

/-!
# Bosonic exchange algebra

The canonical commutation relations provide the `Statistics.boson` instance of
`Common.ExchangeAlgebra`. Since `Bosonic.comm` is already the bosonic specialization of
`Common.exchangeCommutator`, no additional bridge theorem is required.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Statistics.boson Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    simpa [comm] using comm_annihilate_create (Mode := Mode) i j
  annihilate_annihilate i j := by
    simpa [comm] using comm_annihilate_annihilate (Mode := Mode) i j
  create_create i j := by
    simpa [comm] using comm_create_create (Mode := Mode) i j

end Bosonic
end SecondQuantization
