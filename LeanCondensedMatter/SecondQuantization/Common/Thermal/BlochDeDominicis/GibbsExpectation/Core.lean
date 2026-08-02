import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Finite Gibbs expectations from density operators

The normalized Gibbs expectation on a finite configuration space is the canonical expectation of
the trace-class density operator `finiteGibbsDensityOperator`. The old implementation through an
arbitrary complex weighted diagonal functional has been removed from this layer: positivity,
normalization, and linearity now come from the density-state API.

The unnormalized trace identities remain coordinate statements about `traceFock`, `weightedTrace`,
and the free diagonal evolution. They are still used by KMS and Bloch–de Dominicis proofs, but no
longer define the normalized state.
-/

namespace SecondQuantization
namespace Common

open scoped Classical

variable {Config : Type*} [Fintype Config]

/-- The complex Boltzmann weight `e^{-βE(n)}` appearing in algebraic trace formulas. -/
noncomputable def boltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) : ℂ :=
  Complex.exp (((-β) * energy n : ℝ) : ℂ)

omit [Fintype Config] in
/-- The real positive Boltzmann weight used by the density operator casts to the algebraic complex
Boltzmann weight. -/
theorem finiteBoltzmannWeight_cast_eq_boltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) :
    ((finiteBoltzmannWeight energy β n : ℝ) : ℂ) = boltzmannWeight energy β n := by
  rw [finiteBoltzmannWeight, boltzmannWeight, Complex.ofReal_exp]

omit [Fintype Config] in
/-- `diagonalEvolution` is diagonal with the complex Boltzmann weights. -/
theorem matrixCoeff_diagonalEvolution (energy : Config → ℝ) (β : ℝ) (m n : Config) :
    matrixCoeff (diagonalEvolution energy (-β)) m n =
      if m = n then boltzmannWeight energy β m else 0 := by
  rw [matrixCoeff, diagonalEvolution_basisState, boltzmannWeight]
  by_cases h : m = n
  · simp only [if_pos h]
    rw [h, smul_basisState_apply_self]
  · simp only [if_neg h]
    exact smul_basisState_apply_of_ne _ (Ne.symm h)

/-- `Tr[e^{-βH₀}A]` is the Boltzmann-weighted diagonal trace of `A`. -/
theorem traceFock_diagonalEvolution_comp_eq_weightedTrace (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock ((diagonalEvolution energy (-β)).comp A) = weightedTrace (boltzmannWeight energy β) A
    := by
  simp only [traceFock, weightedTrace, matrixCoeff_comp, matrixCoeff_diagonalEvolution, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The trace of the free diagonal evolution is the complex Boltzmann weight sum. -/
theorem traceFock_diagonalEvolution_eq_weightSum (energy : Config → ℝ) (β : ℝ) :
    traceFock (diagonalEvolution energy (-β)) = weightSum (boltzmannWeight energy β) := by
  simp only [traceFock, weightSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [matrixCoeff_diagonalEvolution]
  simp

variable [Nonempty Config]

/-- The normalized finite Gibbs expectation, defined by the canonical Gibbs density operator. -/
noncomputable def gibbsExpectation (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  finiteGibbsExpectation energy β A

/-- During migration, the density-state expectation can still be evaluated by the former normalized
coordinate formula. This is a theorem, not the definition of the state. -/
theorem gibbsExpectation_eq_normalizedWeightedDiagonal (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β A =
      normalizedWeightedDiagonal (boltzmannWeight energy β) A := by
  rw [gibbsExpectation, finiteGibbsExpectation_eq_sum, normalizedWeightedDiagonal,
    weightedTrace, weightSum]
  have hZcast : ((finitePartitionFunction energy β : ℝ) : ℂ) =
      ∑ n : Config, boltzmannWeight energy β n := by
    rw [finitePartitionFunction, tsum_fintype]
    push_cast
    exact Finset.sum_congr rfl fun n _ =>
      finiteBoltzmannWeight_cast_eq_boltzmannWeight energy β n
  have hZne : ((finitePartitionFunction energy β : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (finitePartitionFunction_pos energy β))
  rw [← hZcast]
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← finiteBoltzmannWeight_cast_eq_boltzmannWeight energy β n]
  push_cast
  field_simp

/-- The Gibbs expectation bundled as a complex linear map. -/
noncomputable def gibbsExpectationLinearMap (energy : Config → ℝ) (β : ℝ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  finiteGibbsExpectationLinearMap energy β

@[simp]
theorem gibbsExpectationLinearMap_apply (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectationLinearMap energy β A = gibbsExpectation energy β A :=
  rfl

/-- The Gibbs expectation is normalized without an additional partition-function hypothesis. -/
@[simp]
theorem gibbsExpectation_id (energy : Config → ℝ) (β : ℝ) :
    gibbsExpectation energy β
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1 :=
  finiteGibbsExpectation_id energy β

@[simp]
theorem gibbsExpectation_add (energy : Config → ℝ) (β : ℝ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (A + B) =
      gibbsExpectation energy β A + gibbsExpectation energy β B :=
  (gibbsExpectationLinearMap energy β).map_add A B

@[simp]
theorem gibbsExpectation_smul (energy : Config → ℝ) (β : ℝ) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (c • A) = c * gibbsExpectation energy β A := by
  change gibbsExpectationLinearMap energy β (c • A) =
    c * gibbsExpectationLinearMap energy β A
  simpa only [smul_eq_mul] using (gibbsExpectationLinearMap energy β).map_smul c A

@[simp]
theorem gibbsExpectation_zero (energy : Config → ℝ) (β : ℝ) :
    gibbsExpectation energy β (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 :=
  (gibbsExpectationLinearMap energy β).map_zero

/-- Gibbs expectation distributes across list sums through its linear-map structure. -/
theorem gibbsExpectation_list_sum (energy : Config → ℝ) (β : ℝ)
    (L : List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    gibbsExpectation energy β L.sum = (L.map (gibbsExpectation energy β)).sum := by
  induction L with
  | nil => simp
  | cons A T ih => simp [List.sum_cons, ih]

end Common
end SecondQuantization
