import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Finite Gibbs expectation bridge

Finite Gibbs states are the finite specialization of the generic pure-point Gibbs construction.
This module owns the SecondQuantization-specific adapter that transports algebraic Fock
endomorphisms to the canonical finite Hilbert Gibbs density-state expectation, together with
its normalized diagonal-probability formula. Trace and operator-integral formulas live downstream.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The canonical finite Gibbs expectation, bundled as a complex linear map on algebraic Fock
endomorphisms.  The state itself is the generic finite pure-point Gibbs density operator. -/
noncomputable def finiteGibbsExpectationLinearMap (energy : Config → ℝ) (β : ℝ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  (eigenbasisGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β
        (eigenbasisGibbsSummable_of_finite energy β)).expectation.toLinearMap.comp
    (finiteHilbertOperatorAlgEquiv (Config := Config)).toLinearMap

/-- The canonical finite Gibbs expectation of an algebraic Fock operator. -/
noncomputable def finiteGibbsExpectation (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  finiteGibbsExpectationLinearMap energy β A

@[simp]
theorem finiteGibbsExpectation_id (energy : Config → ℝ) (β : ℝ) :
    finiteGibbsExpectation energy β
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1 := by
  rw [finiteGibbsExpectation, finiteGibbsExpectationLinearMap, LinearMap.comp_apply]
  change
    (eigenbasisGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β
        (eigenbasisGibbsSummable_of_finite energy β)).expectation
        (finiteHilbertOperatorAlgEquiv
          (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) = 1
  rw [← Module.End.one_eq_id, map_one]
  exact (eigenbasisGibbsDensityOperator
    (finiteHilbertBasis (Config := Config)) energy β
        (eigenbasisGibbsSummable_of_finite energy β)).expectation_id

/-- The density-state Gibbs expectation is the normalized pure-point probability weighted diagonal
sum. -/
theorem finiteGibbsExpectation_eq_sum (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      ∑ n : Config, (eigenbasisGibbsProbability energy β n : ℂ) * matrixCoeff A n n := by
  classical
  rw [finiteGibbsExpectation, finiteGibbsExpectationLinearMap, LinearMap.comp_apply]
  rw [(eigenbasisGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β
      (eigenbasisGibbsSummable_of_finite energy β)).expectation_eq_tsum_diagonal
        (finiteHilbertOperatorAlgEquiv A)
        (finiteHilbertBasis (Config := Config))
        (eigenbasisGibbsProbability energy β)
        (eigenbasisGibbsDensityOperator_apply_basis
          (finiteHilbertBasis (Config := Config)) energy β
          (eigenbasisGibbsSummable_of_finite energy β))]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro n _
  simp only [finiteHilbertBasis_apply]
  congr 1
  change inner ℂ (EuclideanSpace.single n 1)
    (finiteHilbertOperatorAlgEquiv A (finiteHilbertBasisState n)) = matrixCoeff A n n
  rw [EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  exact finiteHilbertOperator_basis_apply A n n

end
end Common
end SecondQuantization
