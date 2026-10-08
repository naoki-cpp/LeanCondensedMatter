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
  calc
    Combinatorics.powerSeriesMomentSetFunction (α := Fin N)
        (PowerSeries.normalizeByConstantCoeff
          (dysonPartitionSeries ε β (quarticInteraction g))) hZ =
        Common.dysonTraceVertexMomentSetFunction
          (fermionEnergy ε) β (quarticInteraction g) := by
      simpa only [dysonPartitionSeries] using
        (Common.powerSeriesMomentSetFunction_normalizeByConstantCoeff_dysonTraceSeries_eq_dysonTraceVertexMomentSetFunction
          (α := Fin N) (fermionEnergy ε) β (quarticInteraction g) hZ)
    _ = (quarticWickDiagramMultiplicativeWeight (N := N) ε β g).normalizedObjectMoment := by
      ext S
      change
        Common.dysonTraceVertexMoment (fermionEnergy ε) β (quarticInteraction g) S =
          ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
      exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g S

end Fermionic
end SecondQuantization
