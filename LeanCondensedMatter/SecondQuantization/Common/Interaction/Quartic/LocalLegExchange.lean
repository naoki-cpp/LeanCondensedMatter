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

/-- Scalar coefficient in the exchange bracket of two local legs selected from quartic vertices. -/
def quarticLocalLegExchangeCoeff (s : Statistics) (q q' : QuarticVertexLabel Mode)
    (l l' : Fin 4) : ℂ :=
  match quarticLocalLeg q l, quarticLocalLeg q' l' with
  | .create i, .annihilate j => if i = j then -(s.zetaInt : ℂ) else 0
  | .annihilate i, .create j => if i = j then 1 else 0
  | _, _ => 0

/-- Two local quartic legs have a scalar exchange bracket determined by statistics and leg semantics. -/
theorem exchangeCommutator_quarticLocalLegOperator (s : Statistics) [ExchangeAlgebra s Mode Config]
    (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    exchangeCommutator s
        (quarticLocalLegOperator
          (ExchangeAlgebra.create (s := s) (Config := Config))
          (ExchangeAlgebra.annihilate (s := s) (Config := Config)) q l)
        (quarticLocalLegOperator
          (ExchangeAlgebra.create (s := s) (Config := Config))
          (ExchangeAlgebra.annihilate (s := s) (Config := Config)) q' l') =
      quarticLocalLegExchangeCoeff s q q' l l' •
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
  simp only [quarticLocalLegOperator, quarticLocalLegExchangeCoeff]
  generalize quarticLocalLeg q l = a
  generalize quarticLocalLeg q' l' = b
  cases a <;> cases b <;>
    simp [ExchangeAlgebra.create_create, ExchangeAlgebra.annihilate_annihilate,
      ExchangeAlgebra.annihilate_create, exchangeCommutator_create_annihilate]

end Common
end SecondQuantization
