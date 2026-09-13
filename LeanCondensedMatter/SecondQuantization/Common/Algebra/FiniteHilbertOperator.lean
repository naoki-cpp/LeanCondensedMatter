import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Finite Hilbert realization of algebraic Fock operators

This module owns the representation-theoretic bridge from a finite algebraic Fock basis to its
canonical Euclidean Hilbert realization. The construction is independent of any thermal state:
it provides the finite Hilbert basis, the algebraic-to-Hilbert equivalence, and the canonical
algebra equivalence transporting algebraic endomorphisms to bounded operators.
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

/-- Canonical transport of algebraic Fock endomorphisms to bounded finite-Hilbert operators.

The first algebra equivalence is conjugation by `finiteHilbertFockEquiv`; the second is the
finite-dimensional equivalence between linear and continuous linear endomorphisms. -/
noncomputable def finiteHilbertOperatorAlgEquiv :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) ≃ₐ[ℂ]
      (FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config) :=
  ((finiteHilbertFockEquiv (Config := Config)).conjAlgEquiv ℂ).trans
    (Module.End.toContinuousLinearMap (FiniteHilbertFock Config))

/-- The bounded operator induced by an algebraic Fock endomorphism in finite dimensions. -/
noncomputable def finiteHilbertOperator
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config :=
  finiteHilbertOperatorAlgEquiv A

@[simp]
theorem finiteHilbertOperator_equiv_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (x : AlgebraicFock Config) :
    finiteHilbertOperator A (finiteHilbertFockEquiv x) = finiteHilbertFockEquiv (A x) := by
  change
    ((finiteHilbertFockEquiv (Config := Config)).toLinearMap.comp
      (A.comp (finiteHilbertFockEquiv (Config := Config)).symm.toLinearMap))
        (finiteHilbertFockEquiv x) = finiteHilbertFockEquiv (A x)
  simp

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
  simpa [finiteHilbertOperator] using
    map_add (finiteHilbertOperatorAlgEquiv (Config := Config)) A B

@[simp]
theorem finiteHilbertOperator_smul (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperator (c • A) = c • finiteHilbertOperator A := by
  simpa [finiteHilbertOperator] using
    map_smul (finiteHilbertOperatorAlgEquiv (Config := Config)) c A

@[simp]
theorem finiteHilbertOperator_id :
    finiteHilbertOperator (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
      ContinuousLinearMap.id ℂ (FiniteHilbertFock Config) := by
  change
    finiteHilbertOperatorAlgEquiv
        (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
      ContinuousLinearMap.id ℂ (FiniteHilbertFock Config)
  rw [← Module.End.one_eq_id, ← ContinuousLinearMap.one_def]
  exact map_one (finiteHilbertOperatorAlgEquiv (Config := Config))

/-- Transport of algebraic Fock endomorphisms to bounded Hilbert operators, bundled linearly. -/
noncomputable def finiteHilbertOperatorLinearMap :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ]
      (FiniteHilbertFock Config →L[ℂ] FiniteHilbertFock Config) :=
  (finiteHilbertOperatorAlgEquiv (Config := Config)).toLinearMap

@[simp]
theorem finiteHilbertOperatorLinearMap_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteHilbertOperatorLinearMap A = finiteHilbertOperator A :=
  rfl

end
end Common
end SecondQuantization
