import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperator
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Finite Gibbs expectation bridge

Finite Gibbs states are the finite specialization of the generic pure-point Gibbs construction.
This module keeps only the SecondQuantization-specific adapter that transports algebraic Fock
operators to the finite Hilbert realization, together with the resulting coordinate formulas.
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
  (finitePurePointGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β).expectation.toLinearMap.comp
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
  exact (finitePurePointGibbsDensityOperator
    (finiteHilbertBasis (Config := Config)) energy β).expectation_id

/-- Scalar multiplication passes through the canonical finite Gibbs expectation. -/
@[simp]
theorem finiteGibbsExpectation_smul (energy : Config → ℝ) (β : ℝ) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β (c • A) = c * finiteGibbsExpectation energy β A := by
  change (finiteGibbsExpectationLinearMap energy β) (c • A) =
    c * (finiteGibbsExpectationLinearMap energy β) A
  rw [map_smul, smul_eq_mul]

/-- The density-state Gibbs expectation is the normalized pure-point probability weighted diagonal
sum. -/
theorem finiteGibbsExpectation_eq_sum (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      ∑ n : Config, (purePointGibbsProbability energy β n : ℂ) * matrixCoeff A n n := by
  classical
  have hbase :=
    (finitePurePointGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β).expectation_eq_sum_diagonal
      (finiteHilbertOperator A)
      (finiteHilbertOrthonormalBasis (Config := Config))
      (purePointGibbsProbability energy β)
      (fun n => by
        simpa using finitePurePointGibbsDensityOperator_apply_basis
          (finiteHilbertBasis (Config := Config)) energy β n)
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
  rw [finiteGibbsExpectation, finiteGibbsExpectationLinearMap, LinearMap.comp_apply,
    finiteHilbertOperatorLinearMap_apply]
  calc
    (finitePurePointGibbsDensityOperator
        (finiteHilbertBasis (Config := Config)) energy β).expectation (finiteHilbertOperator A) =
        ∑ n : Config,
          (purePointGibbsProbability energy β n : ℂ) *
            inner ℂ ((finiteHilbertOrthonormalBasis (Config := Config)) n)
              (finiteHilbertOperator A ((finiteHilbertOrthonormalBasis (Config := Config)) n)) :=
      hbase
    _ = ∑ n : Config, (purePointGibbsProbability energy β n : ℂ) * matrixCoeff A n n := by
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
    (hF n).const_mul (purePointGibbsProbability energy β n : ℂ)).symm

end
end Common
end SecondQuantization
