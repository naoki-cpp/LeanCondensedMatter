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

@[simp]
theorem finiteHilbertOperator_equiv_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (x : AlgebraicFock Config) :
    finiteHilbertOperatorAlgEquiv A (finiteHilbertFockEquiv x) =
      finiteHilbertFockEquiv (A x) := by
  change
    ((finiteHilbertFockEquiv (Config := Config)).toLinearMap.comp
      (A.comp (finiteHilbertFockEquiv (Config := Config)).symm.toLinearMap))
        (finiteHilbertFockEquiv x) = finiteHilbertFockEquiv (A x)
  simp

/-- Transported algebraic operators act on canonical finite-Hilbert basis vectors by transporting
the corresponding algebraic basis-state action. -/
theorem finiteHilbertOperator_basisState
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : Config) :
    finiteHilbertOperatorAlgEquiv A (finiteHilbertBasisState n) =
      finiteHilbertFockEquiv (A (basisState n)) := by
  rw [← finiteHilbertFockEquiv_basisState, finiteHilbertOperator_equiv_apply]

@[simp]
theorem finiteHilbertOperator_basis_apply
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    finiteHilbertOperatorAlgEquiv A (finiteHilbertBasisState n) m = matrixCoeff A m n := by
  rw [← finiteHilbertFockEquiv_basisState, finiteHilbertOperator_equiv_apply]
  rfl

end
end Common
end SecondQuantization
