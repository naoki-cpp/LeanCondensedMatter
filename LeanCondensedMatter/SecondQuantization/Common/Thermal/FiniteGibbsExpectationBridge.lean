import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator
import LeanCondensedMatter.QuantumTheory.FiniteDensityOperatorExpectationTraceClass

set_option linter.style.header false

/-!
# Coordinate formula for finite Gibbs density-state expectations

This module is the migration bridge between the canonical density-operator expectation and the old
finite occupation-basis weighted sums. It will be used to move callers before the old functional
stack is deleted.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory.TraceClass

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The density-state Gibbs expectation is the normalized Boltzmann-weighted diagonal sum. -/
theorem finiteGibbsExpectation_eq_sum (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      ∑ n : Config,
        (((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ) *
          matrixCoeff A n n := by
  classical
  have hbase := (finiteGibbsDensityOperator energy β).expectation_eq_sum_diagonal
    (finiteHilbertOperator A)
    (finiteHilbertOrthonormalBasis (Config := Config))
    (fun n => (finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n)
    (fun n => by simpa using finiteGibbsDensityOperator_apply_basis energy β n)
  have hinner (n : Config) :
      inner ℂ ((finiteHilbertOrthonormalBasis (Config := Config)) n)
        (finiteHilbertOperator A ((finiteHilbertOrthonormalBasis (Config := Config)) n)) =
        matrixCoeff A n n := by
    rw [finiteHilbertOrthonormalBasis_apply]
    change inner ℂ (EuclideanSpace.single n 1)
      (finiteHilbertOperator A (finiteHilbertBasisState n)) = matrixCoeff A n n
    rw [EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    exact finiteHilbertOperator_basis_apply A n n
  rw [finiteGibbsExpectation]
  calc
    (finiteGibbsDensityOperator energy β).expectation (finiteHilbertOperator A) =
        ∑ n : Config,
          ((((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ) *
            inner ℂ ((finiteHilbertOrthonormalBasis (Config := Config)) n)
              (finiteHilbertOperator A ((finiteHilbertOrthonormalBasis (Config := Config)) n))) :=
      hbase
    _ = ∑ n : Config,
        (((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ) *
          matrixCoeff A n n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hinner n]

end
end Common
end SecondQuantization
