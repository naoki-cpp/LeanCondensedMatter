import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.Pi

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Finite-configuration Gibbs density operators

A finite occupation/configuration basis carries a canonical Euclidean Hilbert-space realization.
Positive Boltzmann weights on that basis therefore define a genuine density operator, not merely a
normalized coordinate functional.

This Hilbert realization is introduced separately from the existing finite analytic Dyson
realization, which currently uses the sup-norm function space. The destructive replacement of that
analytic representation is deferred until its operator-continuity proofs and all callers migrate in
one package; no compatibility alias between the two spaces is introduced here.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory

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

/-- The canonical finite Gibbs state. -/
noncomputable def finiteGibbsDensityOperator (energy : Config → ℝ) (β : ℝ) :
    QuantumTheory.DensityOperator (FiniteHilbertFock Config) :=
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

/-- The canonical finite Gibbs expectation, bundled as a complex linear map. -/
noncomputable def finiteGibbsExpectationLinearMap (energy : Config → ℝ) (β : ℝ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  (finiteGibbsDensityOperator energy β).expectation.toLinearMap.comp
    (finiteHilbertOperatorLinearMap (Config := Config))

/-- The canonical finite Gibbs expectation of an algebraic Fock operator. -/
noncomputable def finiteGibbsExpectation (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  finiteGibbsExpectationLinearMap energy β A

@[simp]
theorem finiteGibbsExpectationLinearMap_apply (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectationLinearMap energy β A = finiteGibbsExpectation energy β A :=
  rfl

@[simp]
theorem finiteGibbsExpectation_id (energy : Config → ℝ) (β : ℝ) :
    finiteGibbsExpectation energy β
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1 := by
  rw [finiteGibbsExpectation, finiteGibbsExpectationLinearMap, LinearMap.comp_apply,
    finiteHilbertOperatorLinearMap_apply, finiteHilbertOperator_id]
  exact (finiteGibbsDensityOperator energy β).expectation_id

end
end Common
end SecondQuantization
