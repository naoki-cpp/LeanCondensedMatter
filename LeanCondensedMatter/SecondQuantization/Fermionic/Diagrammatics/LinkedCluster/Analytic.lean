import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.Theorem
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticLinkedCluster

set_option linter.style.header false

/-!
# Analytic fermionic linked-cluster theorem

The perturbation layer identifies analytic logarithmic derivatives with coefficients of the formal
Dyson logarithm. This diagrammatic endpoint composes that bridge with the formal connected-diagram
theorem.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Analytic fermionic Dyson linked-cluster theorem: derivatives of the local normalized log
partition function are sums of connected quartic Wick-diagram amplitudes. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    iteratedDeriv n
        (Common.analyticNormalizedLogPartitionFunction
          (fermionEnergy ε) β (quarticInteraction g)) 0 =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  rw [Common.iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_coeff
    (fermionEnergy ε) hβ (quarticInteraction g) n]
  change (n.factorial : ℂ) *
      PowerSeries.coeff n
        (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
    ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
      quarticWickDiagramAmplitude ε β g d.1
  exact factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
    ε β g n hn

end
end Fermionic
end SecondQuantization
