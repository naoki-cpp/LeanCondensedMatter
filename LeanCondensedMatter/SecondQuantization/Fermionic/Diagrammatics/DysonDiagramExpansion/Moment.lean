import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Connected

set_option linter.style.header false

/-!
# Fermionic Dyson partition-series and diagram moments

Identifies the factorial-normalized moments of the normalized fermionic Dyson partition series
with the object moments of the multiplicative quartic Wick-diagram weight. Both the replica and
Möbius-inversion linked-cluster routes consume this same statistics-specific boundary.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The normalized fermionic Dyson partition-series moments are precisely the normalized
object moments of the quartic Wick-diagram connected decomposition. -/
theorem dysonPartitionSeriesMoment_eq_wickDiagramObjectMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {N : ℕ}
    (hZ : PowerSeries.constantCoeff
      (PowerSeries.normalizeByConstantCoeff
        (dysonPartitionSeries ε β (quarticInteraction g))) = 1) :
    Combinatorics.powerSeriesMomentSetFunction (α := Fin N)
        (PowerSeries.normalizeByConstantCoeff
          (dysonPartitionSeries ε β (quarticInteraction g))) hZ =
      (quarticWickDiagramMultiplicativeWeight (N := N) ε β g).normalizedObjectMoment := by
  rw [Combinatorics.powerSeriesMomentSetFunction_eq_iff]
  intro S
  change
    (S.card.factorial : ℂ) *
        PowerSeries.coeff S.card
          (PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g))) =
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
  rw [← dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g S]
  simp only [PowerSeries.coeff_normalizeByConstantCoeff, dysonPartitionSeries,
    Common.coeff_dysonTraceSeries, Common.dysonTraceVertexMoment,
    Common.normalizedDysonTraceCoeff, div_eq_mul_inv]
  ring

end Fermionic
end SecondQuantization
