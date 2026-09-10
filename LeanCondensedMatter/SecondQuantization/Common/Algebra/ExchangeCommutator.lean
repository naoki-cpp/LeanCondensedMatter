import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics

set_option linter.style.header false

/-!
# Statistics-indexed exchange commutator

`Analysis.Operator.ZetaCommutator` owns the representation-independent bracket algebra. This module
only specializes it to `AlgebraicFock` and to the bosonic/fermionic exchange sign.
-/

namespace SecondQuantization
namespace Common

/-- The raw fixed-sign bracket on algebraic Fock-space endomorphisms. -/
noncomputable abbrev zetaCommutator {Config : Type*} (ζ : ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  LinearMap.zetaCommutator ζ A B

/-- The exchange commutator with the sign selected by `s`. -/
noncomputable def exchangeCommutator {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  zetaCommutator (s.zetaInt : ℂ) A B

/-- Scalar multiples factor out of the exchange bracket. -/
theorem zetaCommutator_smul_smul {Config : Type*} (ζ c d : ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    zetaCommutator ζ (c • A) (d • B) = (c * d) • zetaCommutator ζ A B :=
  LinearMap.zetaCommutator_smul_smul ζ c d A B

/-- Reorder `A ∘ B` when its `ζ`-commutator is the identity. -/
theorem comp_eq_id_add_of_zetaCommutator_eq_id {Config : Type*} (ζ : ℂ)
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : zetaCommutator ζ A B = LinearMap.id) :
    A.comp B = LinearMap.id + ζ • (B.comp A) :=
  LinearMap.comp_eq_add_smul_comp_of_zetaCommutator_eq ζ h

end Common
end SecondQuantization
