import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteWeightedTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Finite Gibbs expectations from density operators

The normalized Gibbs expectation on a finite configuration space is the canonical expectation of
the trace-class density operator `finiteGibbsDensityOperator`. Positivity, normalization, and
linearity come from the density-state API.

The unnormalized trace identities remain coordinate statements about `traceFock`, `weightedTrace`,
and the free diagonal evolution. The normalized Bloch–de Dominicis layer uses only their physical
trace-ratio combination; comparison with the temporary `normalizedWeightedDiagonal` coordinate
formula lives in `FiniteGibbsCoordinateBridge.lean`.
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

/-- The canonical finite Gibbs expectation is the normalized physical trace
`Tr[e^{-βH₀}A] / Tr[e^{-βH₀}]`. -/
theorem finiteGibbsExpectation_eq_trace_div (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      traceFock ((diagonalEvolution energy (-β)).comp A) /
        traceFock (diagonalEvolution energy (-β)) := by
  rw [finiteGibbsExpectation_eq_sum, traceFock_diagonalEvolution_comp_eq_weightedTrace,
    traceFock_diagonalEvolution_eq_weightSum, weightedTrace, weightSum]
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
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [← finiteBoltzmannWeight_cast_eq_boltzmannWeight energy β n]
  push_cast
  field_simp

end Common
end SecondQuantization
