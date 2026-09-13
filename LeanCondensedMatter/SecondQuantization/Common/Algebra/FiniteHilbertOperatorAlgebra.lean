import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator

set_option linter.style.header false

/-!
# Multiplicative finite-Hilbert operator transport

The finite-dimensional transport from algebraic Fock endomorphisms to bounded operators is the
algebra equivalence `finiteHilbertOperatorAlgEquiv`. This module keeps the composition theorem and
algebra-homomorphism view used by downstream code.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

@[simp]
theorem finiteHilbertOperator_comp
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperator (A.comp B) =
      (finiteHilbertOperator A).comp (finiteHilbertOperator B) := by
  change
    finiteHilbertOperatorAlgEquiv (A.comp B) =
      (finiteHilbertOperatorAlgEquiv A).comp (finiteHilbertOperatorAlgEquiv B)
  rw [← Module.End.mul_eq_comp, ← ContinuousLinearMap.mul_def]
  exact map_mul (finiteHilbertOperatorAlgEquiv (Config := Config)) A B

/-- Transport of algebraic Fock endomorphisms to bounded Hilbert operators, viewed as an algebra
homomorphism. -/
noncomputable def finiteHilbertOperatorAlgHom :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₐ[ℂ]
      (FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config) :=
  (finiteHilbertOperatorAlgEquiv (Config := Config)).toAlgHom

end
end Common
end SecondQuantization
