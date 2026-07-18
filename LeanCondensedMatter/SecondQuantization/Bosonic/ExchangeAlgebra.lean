import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Common.ExchangeAlgebra

set_option linter.style.header false

/-!
# The bosonic `Common.ExchangeAlgebra` instance

The bosonic mirror of `Fermionic/ExchangeAlgebra.lean`: instantiates `Common.ExchangeAlgebra` at
`Statistics.boson` for `Occupation Mode`, from `CCR.lean`'s commutation facts
(`comm_annihilate_create`/`_annihilate_annihilate`/`_create_create`) via the bridging fact that
`Common.exchangeCommutator Statistics.boson` and `comm` are the same operator, for any two
operators.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **`Common.exchangeCommutator Statistics.boson = comm`**: CCR's commutator is exactly the
`ζ = 1` case of the graded commutator, for arbitrary operators `A`, `B`. -/
theorem exchangeCommutator_boson_eq_comm
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :
    Common.exchangeCommutator Statistics.boson A B = comm A B := by
  rw [Common.exchangeCommutator, Statistics.zetaInt_boson, Int.cast_one, Common.zetaCommutator,
    one_smul]
  rfl

/-- **The bosonic exchange algebra.** -/
noncomputable instance exchangeAlgebra :
    Common.ExchangeAlgebra Statistics.boson Mode (Occupation Mode) where
  annihilate := annihilate
  create := create
  annihilate_create i j := by
    rw [exchangeCommutator_boson_eq_comm, comm_annihilate_create]
  annihilate_annihilate i j := by
    rw [exchangeCommutator_boson_eq_comm, comm_annihilate_annihilate]
  create_create i j := by
    rw [exchangeCommutator_boson_eq_comm, comm_create_create]

end Bosonic
end SecondQuantization
