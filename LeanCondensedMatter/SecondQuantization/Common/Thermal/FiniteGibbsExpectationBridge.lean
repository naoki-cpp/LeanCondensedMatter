import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite

set_option linter.style.header false

/-!
# Coordinate formula for finite Gibbs density-state expectations

This module identifies the canonical density-operator expectation with finite occupation-basis
weighted sums.
-/

namespace SecondQuantization
namespace Common

noncomputable section

open QuantumTheory

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- Scalar multiplication passes through the canonical finite Gibbs expectation. -/
@[simp]
theorem finiteGibbsExpectation_smul (energy : Config → ℝ) (β : ℝ) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β (c • A) = c * finiteGibbsExpectation energy β A := by
  change (finiteGibbsExpectationLinearMap energy β) (c • A) =
    c * (finiteGibbsExpectationLinearMap energy β) A
  rw [map_smul, smul_eq_mul]

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

/-- The canonical finite Gibbs expectation commutes with coefficientwise finite operator
integration. -/
theorem finiteGibbsExpectation_operatorIntervalIntegral
    (energy : Config → ℝ) (β : ℝ)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ)
    (hF : ∀ n : Config, IntervalIntegrable
      (fun τ => matrixCoeff (F τ) n n) MeasureTheory.volume a b) :
    finiteGibbsExpectation energy β (operatorIntervalIntegral F a b) =
      ∫ τ in a..b, finiteGibbsExpectation energy β (F τ) := by
  simp_rw [finiteGibbsExpectation_eq_sum, matrixCoeff_operatorIntervalIntegral,
    ← intervalIntegral.integral_const_mul]
  exact (intervalIntegral.integral_finsetSum fun n _ =>
    (hF n).const_mul
      ((((finitePartitionFunction energy β)⁻¹ * finiteBoltzmannWeight energy β n : ℝ) : ℂ))).symm

/-- The finite Gibbs density-state expectation commutes with coefficientwise finite operator
integration after transporting algebraic operators to the finite Hilbert realization. -/
theorem finiteGibbsDensityOperator_expectation_operatorIntervalIntegral
    (energy : Config → ℝ) (β : ℝ)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ)
    (hF : ∀ n : Config, IntervalIntegrable
      (fun τ => matrixCoeff (F τ) n n) MeasureTheory.volume a b) :
    (finiteGibbsDensityOperator energy β).expectation
        (finiteHilbertOperator (operatorIntervalIntegral F a b)) =
      ∫ τ in a..b,
        (finiteGibbsDensityOperator energy β).expectation (finiteHilbertOperator (F τ)) := by
  simpa [finiteGibbsExpectation, finiteGibbsExpectationLinearMap] using
    finiteGibbsExpectation_operatorIntervalIntegral energy β F a b hF

end
end Common
end SecondQuantization
