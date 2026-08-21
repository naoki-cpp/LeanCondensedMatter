import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator
import Mathlib.Algebra.Algebra.Hom

set_option linter.style.header false

/-!
# Multiplicative finite-Hilbert operator transport

The finite-dimensional transport from algebraic Fock endomorphisms to bounded operators is not
only complex-linear: conjugation by `finiteHilbertFockEquiv` preserves identity and composition.
This module exposes that multiplicative structure as an algebra homomorphism.
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
  apply ContinuousLinearMap.ext
  intro x
  rw [← (finiteHilbertFockEquiv (Config := Config)).apply_symm_apply x]
  let y := (finiteHilbertFockEquiv (Config := Config)).symm x
  change
    finiteHilbertOperator (A.comp B) (finiteHilbertFockEquiv y) =
      finiteHilbertOperator A (finiteHilbertOperator B (finiteHilbertFockEquiv y))
  rw [finiteHilbertOperator_equiv_apply]
  rw [finiteHilbertOperator_equiv_apply]
  rw [finiteHilbertOperator_equiv_apply]
  rfl

/-- Transport of algebraic Fock endomorphisms to bounded Hilbert operators, bundled as a
complex algebra homomorphism. -/
noncomputable def finiteHilbertOperatorAlgHom :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₐ[ℂ]
      (FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config) :=
  AlgHom.ofLinearMap
    (finiteHilbertOperatorLinearMap (Config := Config))
    (by
      change finiteHilbertOperator
          (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
        ContinuousLinearMap.id ℂ (FiniteHilbertFock Config)
      exact finiteHilbertOperator_id)
    (fun A B => by
      change finiteHilbertOperator (A.comp B) =
        (finiteHilbertOperator A).comp (finiteHilbertOperator B)
      exact finiteHilbertOperator_comp A B)

@[simp]
theorem finiteHilbertOperatorAlgHom_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperatorAlgHom A = finiteHilbertOperator A :=
  rfl

end
end Common
end SecondQuantization
