import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Finite Gibbs coordinate formulas

This module owns the finite-coordinate realization of the canonical pure-point Gibbs expectation:
complex Boltzmann weights, diagonal-evolution trace formulas, the physical trace-ratio identity, and
the comparison with the normalized weighted diagonal functional.

These facts are thermal infrastructure independent of Bloch--de Dominicis. Pairing-specific modules
consume this API downstream; perturbative finite-coordinate calculations may use it directly.
-/

namespace SecondQuantization
namespace Common

open scoped Classical
open QuantumTheory

variable {Config : Type*} [Fintype Config]

/-- The complex Boltzmann weight `e^{-βE(n)}` appearing in algebraic trace formulas. -/
noncomputable def boltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) : ℂ :=
  Complex.exp (((-β) * energy n : ℝ) : ℂ)

omit [Fintype Config] in
private theorem purePointBoltzmannWeight_cast_eq_boltzmannWeight
    (energy : Config → ℝ) (β : ℝ) (n : Config) :
    ((purePointBoltzmannWeight energy β n : ℝ) : ℂ) = boltzmannWeight energy β n := by
  rw [purePointBoltzmannWeight, boltzmannWeight, Complex.ofReal_exp]

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
  rw [traceFock_eq_sum_matrixCoeff, weightedTrace_eq_sum_matrixCoeff]
  simp only [matrixCoeff_comp, matrixCoeff_diagonalEvolution, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The trace of the free diagonal evolution is the complex Boltzmann weight sum. -/
theorem traceFock_diagonalEvolution_eq_weightSum (energy : Config → ℝ) (β : ℝ) :
    traceFock (diagonalEvolution energy (-β)) = weightSum (boltzmannWeight energy β) := by
  rw [traceFock_eq_sum_matrixCoeff]
  simp only [weightSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [matrixCoeff_diagonalEvolution]
  simp

/-- On a finite configuration type, the canonical real pure-point partition function agrees,
after coercion to `ℂ`, with the finite complex Boltzmann-coordinate sum. -/
theorem coe_purePointPartitionFunction_eq_sum_boltzmannWeight
    (energy : Config → ℝ) (β : ℝ) :
    ((purePointPartitionFunction energy β : ℝ) : ℂ) =
      ∑ n : Config, boltzmannWeight energy β n := by
  rw [purePointPartitionFunction, tsum_fintype]
  push_cast
  exact Finset.sum_congr rfl fun n _ =>
    purePointBoltzmannWeight_cast_eq_boltzmannWeight energy β n

variable [Nonempty Config]

/-- The finite Gibbs partition trace is nonzero. -/
theorem traceFock_diagonalEvolution_ne_zero (energy : Config → ℝ) (β : ℝ) :
    traceFock (diagonalEvolution energy (-β)) ≠ 0 := by
  rw [traceFock_diagonalEvolution_eq_weightSum, weightSum,
    ← coe_purePointPartitionFunction_eq_sum_boltzmannWeight]
  exact_mod_cast (ne_of_gt
    (purePointPartitionFunction_pos energy β (purePointGibbsSummable_of_finite energy β)))

/-- The canonical finite Gibbs expectation is the normalized physical trace
`Tr[e^{-βH₀}A] / Tr[e^{-βH₀}]`. -/
theorem finiteGibbsExpectation_eq_trace_div (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      traceFock ((diagonalEvolution energy (-β)).comp A) /
        traceFock (diagonalEvolution energy (-β)) := by
  rw [finiteGibbsExpectation_eq_sum, traceFock_diagonalEvolution_comp_eq_weightedTrace,
    traceFock_diagonalEvolution_eq_weightSum, weightedTrace_eq_sum_matrixCoeff, weightSum]
  simp_rw [purePointGibbsProbability]
  have hZcast : ((purePointPartitionFunction energy β : ℝ) : ℂ) =
      ∑ n : Config, boltzmannWeight energy β n :=
    coe_purePointPartitionFunction_eq_sum_boltzmannWeight energy β
  have hZne : ((purePointPartitionFunction energy β : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (purePointPartitionFunction_pos energy β (purePointGibbsSummable_of_finite energy β)))
  rw [← hZcast]
  field_simp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [← purePointBoltzmannWeight_cast_eq_boltzmannWeight energy β n]
  push_cast
  field_simp

/-- The canonical finite Gibbs expectation agrees with the normalized Boltzmann-weighted diagonal
coordinate formula. -/
theorem finiteGibbsExpectation_eq_normalizedWeightedDiagonal (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    finiteGibbsExpectation energy β A =
      normalizedWeightedDiagonal (boltzmannWeight energy β) A := by
  rw [finiteGibbsExpectation_eq_trace_div, normalizedWeightedDiagonal_eq_weightedTrace_div,
    traceFock_diagonalEvolution_comp_eq_weightedTrace,
    traceFock_diagonalEvolution_eq_weightSum]

end Common
end SecondQuantization
