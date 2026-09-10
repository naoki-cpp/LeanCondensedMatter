import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics

set_option linter.style.header false

/-!
# Statistics-indexed exchange commutator

The representation-independent bracket algebra lives in `Analysis.Operator.ZetaCommutator`.
This module only selects its scalar from `Statistics`.
-/

namespace SecondQuantization
namespace Common

/-- The `ζ`-commutator with `ζ` selected by the exchange statistics `s`. -/
noncomputable def exchangeCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Statistics) (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  LinearMap.zetaCommutator (s.zetaInt : ℂ) A B

end Common
end SecondQuantization
