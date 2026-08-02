import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.QuantumTheory.DiagonalDensityLemmasTraceClass
import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationTraceClass
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.Pi

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Finite-configuration Gibbs density operators

A finite occupation/configuration basis carries a canonical Euclidean Hilbert-space realization.
Positive Boltzmann weights on that basis therefore define a genuine trace-class density operator,
not merely a normalized coordinate functional.

This Hilbert realization is introduced separately from the existing finite analytic Dyson
realization, which currently uses the sup-norm function space. The destructive replacement of that
analytic representation is deferred until its operator-continuity proofs and all callers migrate in
one package; no compatibility alias between the two spaces is introduced here.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory.TraceClass

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

/-- The positive real Boltzmann weight `exp (-β E(n))`. -/
noncomputable def finiteBoltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) : ℝ :=
  Real.exp (-β * energy n)

/-- The real finite partition function. -/
noncomputable def finitePartitionFunction (energy : Config → ℝ) (β : ℝ) : ℝ :=
  ∑' n : Config, finiteBoltzmannWeight energy β n

/-- The finite Boltzmann family has its defining finite sum. -/
theorem hasSum_finiteBoltzmannWeight (energy : Config → ℝ) (β : ℝ) :
    HasSum (finiteBoltzmannWeight energy β) (finitePartitionFunction energy β) := by
  rw [finitePartitionFunction]
  exact (Summable.of_finite : Summable (finiteBoltzmannWeight energy β)).hasSum

variable [Nonempty Config]

/-- The finite partition function is strictly positive. -/
theorem finitePartitionFunction_pos (energy : Config → ℝ) (β : ℝ) :
    0 < finitePartitionFunction energy β := by
  rw [finitePartitionFunction, tsum_fintype]
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The canonical finite Gibbs state as a trace-class density operator. -/
noncomputable def finiteGibbsDensityOperator (energy : Config → ℝ) (β : ℝ) :
    QuantumTheory.TraceClass.DensityOperator (FiniteHilbertFock Config) :=
  diagonalDensityOperator
    (finiteHilbertBasis (Config := Config))
    (finiteBoltzmannWeight energy β)
    Summable.of_finite
    (fun _ => (Real.exp_pos _).le)
    (finitePartitionFunction_pos energy β)

/-- The finite Gibbs density operator acts diagonally with normalized Boltzmann weights. -/
@[simp]
theorem finiteGibbsDensityOperator_apply_basis (energy : Config → ℝ) (β : ℝ) (n : Config) :
    (finiteGibbsDensityOperator energy β).op (finiteHilbertBasisState n) =
      (((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ) •
        finiteHilbertBasisState n := by
  simpa [finiteGibbsDensityOperator, finitePartitionFunction, normalizedDiagonalWeight] using
    diagonalDensityOperator_apply_basis
      (finiteHilbertBasis (Config := Config))
      (finiteBoltzmannWeight energy β)
      (Summable.of_finite : Summable fun n : Config => ‖finiteBoltzmannWeight energy β n‖)
      (fun _ => (Real.exp_pos _).le)
      (finitePartitionFunction_pos energy β) n

/-- The canonical finite Gibbs expectation of an algebraic Fock operator. -/
noncomputable def finiteGibbsExpectation (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  (finiteGibbsDensityOperator energy β).expectation (finiteHilbertOperator A)

end
end Common
end SecondQuantization
