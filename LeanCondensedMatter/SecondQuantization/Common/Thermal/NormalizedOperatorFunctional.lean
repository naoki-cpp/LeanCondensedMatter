import LeanCondensedMatter.Analysis.NormalizedEndomorphismFunctional
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Normalized functionals on algebraic-Fock endomorphisms

The underlying mathematical structure is the general
`NormalizedEndomorphismFunctional` from `Analysis/`.  This module only supplies the
second-quantization specialization to endomorphisms of `AlgebraicFock Config` and retains the
existing Common-facing theorem names.

No positivity, trace, Gibbs, or quasifree property is implied by this base interface.
-/

namespace SecondQuantization
namespace Common

/-- A normalized linear functional on endomorphisms of `AlgebraicFock Config`. -/
abbrev NormalizedOperatorFunctional (Config : Type*) :=
  NormalizedEndomorphismFunctional ℂ (AlgebraicFock Config)

namespace NormalizedOperatorFunctional

variable {Config : Type*}

@[simp]
theorem toLinearMap_apply (F : NormalizedOperatorFunctional Config)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : F.toLinearMap A = F A :=
  NormalizedEndomorphismFunctional.toLinearMap_apply F A

theorem map_add (F : NormalizedOperatorFunctional Config)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    F (A + B) = F A + F B :=
  NormalizedEndomorphismFunctional.map_add F A B

theorem map_smul (F : NormalizedOperatorFunctional Config) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    F (c • A) = c * F A :=
  NormalizedEndomorphismFunctional.map_smul F c A

@[simp]
theorem map_zero (F : NormalizedOperatorFunctional Config) : F 0 = 0 :=
  NormalizedEndomorphismFunctional.map_zero F

theorem map_neg (F : NormalizedOperatorFunctional Config)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : F (-A) = -F A :=
  NormalizedEndomorphismFunctional.map_neg F A

theorem map_sub (F : NormalizedOperatorFunctional Config)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : F (A - B) = F A - F B :=
  NormalizedEndomorphismFunctional.map_sub F A B

end NormalizedOperatorFunctional
end Common
end SecondQuantization
