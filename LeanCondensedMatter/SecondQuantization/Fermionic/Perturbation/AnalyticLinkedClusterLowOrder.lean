import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.LowOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.AnalyticLinkedClusterIdentification

set_option linter.style.header false

/-!
# Low-order analytic fermionic linked-cluster identities

These corollaries identify the first three derivatives of the genuine normalized analytic partition
function logarithm with the same moment-cumulant polynomials as the formal Dyson theorem.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- First derivative of the analytic normalized logarithm. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_order_one
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) :
    iteratedDeriv 1
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 := by
  calc
    iteratedDeriv 1
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
        ((1 : ℕ).factorial : ℂ) *
          PowerSeries.coeff 1
            (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) :=
      iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
        ε hβ (quarticInteraction g) 1
    _ = normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_order_one ε β g

/-- Second derivative of the analytic normalized logarithm, with the disconnected square
subtracted explicitly. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_order_two
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) :
    iteratedDeriv 2
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
      2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 -
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 2 := by
  calc
    iteratedDeriv 2
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
        ((2 : ℕ).factorial : ℂ) *
          PowerSeries.coeff 2
            (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) :=
      iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
        ε hβ (quarticInteraction g) 2
    _ = 2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 -
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 2 :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_order_two ε β g

/-- Third derivative of the analytic normalized logarithm, with all disconnected partitions
subtracted explicitly. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_order_three
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) :
    iteratedDeriv 3
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
      6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 3 -
        6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 +
        2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 3 := by
  calc
    iteratedDeriv 3
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
        ((3 : ℕ).factorial : ℂ) *
          PowerSeries.coeff 3
            (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) :=
      iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
        ε hβ (quarticInteraction g) 3
    _ = 6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 3 -
        6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 +
        2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 3 :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_order_three ε β g

end
end Fermionic
end SecondQuantization
