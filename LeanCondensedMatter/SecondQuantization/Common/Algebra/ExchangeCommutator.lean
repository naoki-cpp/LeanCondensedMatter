import LeanCondensedMatter.Analysis.ScalarExchange.Graded
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics

set_option linter.style.header false

/-!
# Statistics-indexed exchange commutator

The representation-independent bracket algebra lives in `Analysis.ScalarExchange`.
This module only selects its scalar from `Statistics`.
-/

namespace SecondQuantization
namespace Common

/-- The `ζ`-commutator with `ζ` selected by the exchange statistics `s`. -/
noncomputable def exchangeCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Statistics) (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  ScalarExchange.zetaCommutator (s.zetaInt : ℂ) A B

/-- The single-statistics bracket is the equal-parity specialization of
the graded bracket. A mixed pair may have different parities, which is why
the graded bracket is strictly more general than `exchangeCommutator`. -/
theorem exchangeCommutator_eq_gradedCommutator
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Statistics) (A B : V →ₗ[ℂ] V) :
    exchangeCommutator s A B =
      ScalarExchange.gradedCommutator s.parity s.parity A B := by
  cases s <;>
    simp [exchangeCommutator, ScalarExchange.gradedCommutator,
      ScalarExchange.paritySign, Statistics.parity, Statistics.zetaInt]


end Common
end SecondQuantization
