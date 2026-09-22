import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic

set_option linter.style.header false

/-!
# Exchange algebra of quartic local legs

The scalar exchange coefficient of two local quartic legs depends only on their ladder constructors,
modes, and particle statistics. Concrete bosonic and fermionic realizations inherit the same theorem
through `ExchangeAlgebra`.
-/

namespace SecondQuantization
namespace Common

variable {Mode Config : Type*} [DecidableEq Mode]

namespace QuarticLocalLeg

/-- Scalar coefficient in the exchange bracket of two quartic local legs. -/
def exchangeCoeff (s : Statistics) (a b : QuarticLocalLeg Mode) : ℂ :=
  match a, b with
  | .create i, .annihilate j => if i = j then -(s.zetaInt : ℂ) else 0
  | .annihilate i, .create j => if i = j then 1 else 0
  | _, _ => 0

/-- Two quartic local legs have a scalar exchange bracket determined by statistics and leg semantics. -/
theorem exchangeCommutator_operator (s : Statistics) [ExchangeAlgebra s Mode Config]
    (a b : QuarticLocalLeg Mode) :
    exchangeCommutator s
        (a.operator
          (ExchangeAlgebra.create (s := s) (Config := Config))
          (ExchangeAlgebra.annihilate (s := s) (Config := Config)))
        (b.operator
          (ExchangeAlgebra.create (s := s) (Config := Config))
          (ExchangeAlgebra.annihilate (s := s) (Config := Config))) =
      exchangeCoeff s a b •
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
  cases a <;> cases b <;>
    simp [exchangeCoeff, ExchangeAlgebra.create_create, ExchangeAlgebra.annihilate_annihilate,
      ExchangeAlgebra.annihilate_create, exchangeCommutator_create_annihilate]

end QuarticLocalLeg

end Common
end SecondQuantization
