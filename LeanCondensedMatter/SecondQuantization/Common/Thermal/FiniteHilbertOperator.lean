import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.Pi

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Finite Hilbert realization of algebraic Fock operators

This module owns the representation-theoretic bridge from a finite algebraic Fock basis to its
canonical Euclidean Hilbert realization.  The construction is independent of any thermal state:
it provides the finite Hilbert basis, the algebraic-to-Hilbert equivalence, and transport of
algebraic endomorphisms to bounded operators.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The finite-dimensional Hilbert realization of the algebraic Fock basis. -/
abbrev FiniteHilbertFock (Config : Type*) := EuclideanSpace ℂ Config

/-- The standard occupation/configuration basis vector in the finite Hilbert Fock space. -/
noncomputable def finiteHilbertBasisState (n : Config) : FiniteHilbertFock Config :=
  EuclideanSpace.basisFun Config ℂ n

/-- The canonical coordinate orthonormal basis of the finite Hilbert Fock space. -/
noncomputable def finiteHilbertOrthonormalBasis :
    OrthonormalBasis Config ℂ (FiniteHilbertFock Config) :=
  EuclideanSpace.basisFun Config ℂ

/-- The canonical coordinate Hilbert basis of the finite Hilbert Fock space. -/
noncomputable def finiteHilbertBasis :
    HilbertBasis Config ℂ (FiniteHilbertFock Config) :=
  (finiteHilbertOrthonormalBasis (Config := Config)).toHilbertBasis

@[simp]
theorem finiteHilbertOrthonormalBasis_apply (n : Config) :
    finiteHilbertOrthonormalBasis (Config := Config) n = finiteHilbertBasisState n :=
  rfl

@[simp]
theorem finiteHilbertBasis_apply (n : Config) :
    finiteHilbertBasis (Config := Config) n = finiteHilbertBasisState n := by
  have h := congrFun
    (OrthonormalBasis.coe_toHilbertBasis
      (finiteHilbertOrthonormalBasis (Config := Config))) n
  simpa [finiteHilbertBasis, finiteHilbertOrthonormalBasis_apply] using h

/-- The canonical linear equivalence from algebraic Fock vectors to the finite Hilbert realization. -/
noncomputable def finiteHilbertFockEquiv :
    AlgebraicFock Config ≃ₗ[ℂ] FiniteHilbertFock Config :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ Config).trans
    (WithLp.linearEquiv 2 ℂ (Config → ℂ)).symm

@[simp]
theorem finiteHilbertFockEquiv_basisState (n : Config) :
    finiteHilbertFockEquiv (basisState n) = finiteHilbertBasisState n := by
  classical
  simp [finiteHilbertFockEquiv, finiteHilbertBasisState, basisState,
    EuclideanSpace.basisFun_apply]

/-- Conjugate an algebraic Fock endomorphism into the finite Hilbert realization. -/
noncomputable def transportedFiniteHilbertOperatorLinearMap
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    FiniteHilbertFock Config →ₗ[ℂ] FiniteHilbertFock Config :=
  (finiteHilbertFockEquiv (Config := Config)).toLinearMap.comp
    (A.comp (finiteHilbertFockEquiv (Config := Config)).symm.toLinearMap)

/-- The bounded operator induced by an algebraic Fock endomorphism in finite dimensions. -/
noncomputable def finiteHilbertOperator
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config :=
  (transportedFiniteHilbertOperatorLinearMap A).toContinuousLinearMap

@[simp]
theorem finiteHilbertOperator_equiv_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (x : AlgebraicFock Config) :
    finiteHilbertOperator A (finiteHilbertFockEquiv x) = finiteHilbertFockEquiv (A x) := by
  simp [finiteHilbertOperator, transportedFiniteHilbertOperatorLinearMap]

@[simp]
theorem finiteHilbertOperator_basis_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    finiteHilbertOperator A (finiteHilbertBasisState n) m = matrixCoeff A m n := by
  rw [← finiteHilbertFockEquiv_basisState, finiteHilbertOperator_equiv_apply]
  rfl

@[simp]
theorem finiteHilbertOperator_add
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperator (A + B) = finiteHilbertOperator A + finiteHilbertOperator B := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← (finiteHilbertFockEquiv (Config := Config)).apply_symm_apply x]
  calc
    finiteHilbertOperator (A + B)
        (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) =
        finiteHilbertFockEquiv
          ((A + B) ((finiteHilbertFockEquiv (Config := Config)).symm x)) :=
      finiteHilbertOperator_equiv_apply _ _
    _ = finiteHilbertFockEquiv
        (A ((finiteHilbertFockEquiv (Config := Config)).symm x) +
          B ((finiteHilbertFockEquiv (Config := Config)).symm x)) := by
      rw [LinearMap.add_apply]
    _ = finiteHilbertFockEquiv (A ((finiteHilbertFockEquiv (Config := Config)).symm x)) +
        finiteHilbertFockEquiv (B ((finiteHilbertFockEquiv (Config := Config)).symm x)) :=
      map_add _ _ _
    _ = finiteHilbertOperator A
          (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) +
        finiteHilbertOperator B
          (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) := by
      rw [finiteHilbertOperator_equiv_apply, finiteHilbertOperator_equiv_apply]

@[simp]
theorem finiteHilbertOperator_smul (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperator (c • A) = c • finiteHilbertOperator A := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← (finiteHilbertFockEquiv (Config := Config)).apply_symm_apply x]
  calc
    finiteHilbertOperator (c • A)
        (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) =
        finiteHilbertFockEquiv
          ((c • A) ((finiteHilbertFockEquiv (Config := Config)).symm x)) :=
      finiteHilbertOperator_equiv_apply _ _
    _ = finiteHilbertFockEquiv
        (c • A ((finiteHilbertFockEquiv (Config := Config)).symm x)) := by
      rw [LinearMap.smul_apply]
    _ = c • finiteHilbertFockEquiv
        (A ((finiteHilbertFockEquiv (Config := Config)).symm x)) :=
      map_smul _ _ _
    _ = c • finiteHilbertOperator A
        (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) := by
      rw [finiteHilbertOperator_equiv_apply]

@[simp]
theorem finiteHilbertOperator_id :
    finiteHilbertOperator (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
      ContinuousLinearMap.id ℂ (FiniteHilbertFock Config) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← (finiteHilbertFockEquiv (Config := Config)).apply_symm_apply x]
  calc
    finiteHilbertOperator LinearMap.id
        (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) =
        finiteHilbertFockEquiv
          (LinearMap.id ((finiteHilbertFockEquiv (Config := Config)).symm x)) :=
      finiteHilbertOperator_equiv_apply _ _
    _ = finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x) := by
      rw [LinearMap.id_apply]
    _ = (ContinuousLinearMap.id ℂ (FiniteHilbertFock Config))
        (finiteHilbertFockEquiv ((finiteHilbertFockEquiv (Config := Config)).symm x)) := by
      rw [ContinuousLinearMap.id_apply]

/-- Transport of algebraic Fock endomorphisms to bounded Hilbert operators, bundled linearly. -/
noncomputable def finiteHilbertOperatorLinearMap :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ]
      (FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config) where
  toFun := finiteHilbertOperator
  map_add' := finiteHilbertOperator_add
  map_smul' := finiteHilbertOperator_smul

@[simp]
theorem finiteHilbertOperatorLinearMap_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperatorLinearMap A = finiteHilbertOperator A :=
  rfl

end
end Common
end SecondQuantization
