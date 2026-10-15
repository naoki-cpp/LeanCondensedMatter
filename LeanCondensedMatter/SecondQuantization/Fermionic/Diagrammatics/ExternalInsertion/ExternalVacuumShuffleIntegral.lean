import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Combinatorics.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.OrderedVacuum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Integral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity

set_option linter.style.header false

/-!
# Binary shuffle integral for arbitrary external insertions and vacuum data

The fixed external-insertion Dyson integrand is measurably locally bounded. Pairing it with the
continuous fixed-order quartic vacuum integrand allows the general binary ordered-simplex shuffle
identity to separate their integrated contributions. This analytic product theorem depends only
on the independent integrands and their regularity, without slot-split pairing transport.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Summing the binary ordered-simplex shuffles of one arbitrary-external Dyson integrand and
one fixed-order vacuum diagram gives the product of their independent Dyson contributions. -/
theorem sum_slotShuffleExternalInsertionDysonIntegral_eq_mul_orderedVacuum
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {E m k : ℕ} (externalTime : Fin (2 * E) → ℝ)
    (ext : ExternalInsertionWickDiagram Mode E m)
    (x : OrderedQuarticDiagramData (QuarticVertexLabel Mode) k) :
    (∑ shuffle : SlotShuffle m k,
      intervalIntegral.orderedSimplexIntegral (m + k) β
        (shuffle.integrand
          (fun σ => ext.dysonFixedTimeAmplitude ε β g externalTime σ)
          (orderedVacuumDysonIntegrand ε β g x))) =
      ext.dysonAmplitude ε β g externalTime *
        ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
          intervalIntegral.orderedSimplexIntegral k β
            (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) := by
  have hext :
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin m → ℝ => ext.dysonFixedTimeAmplitude ε β g externalTime σ) :=
    ext.measurableLocallyBounded_dysonFixedTimeAmplitude ε β g externalTime
  have hvac :
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin k → ℝ =>
          (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
            flatVertexLegPairingEvaluation ε β x.1 σ x.2) :=
    (intervalIntegral.measurableLocallyBounded_const
      ((-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)))).mul
      (intervalIntegral.Continuous.measurableLocallyBounded
        (continuous_flatVertexLegPairingEvaluation ε β x.1 x.2))
  calc
    _ = intervalIntegral.orderedSimplexIntegral m β
          (fun σ => ext.dysonFixedTimeAmplitude ε β g externalTime σ) *
        intervalIntegral.orderedSimplexIntegral k β
          (orderedVacuumDysonIntegrand ε β g x) :=
      BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
        m k β
        (fun σ => ext.dysonFixedTimeAmplitude ε β g externalTime σ)
        (orderedVacuumDysonIntegrand ε β g x) hext hvac
    _ = _ := by
      unfold orderedVacuumDysonIntegrand
      rw [ext.orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g externalTime,
        intervalIntegral.orderedSimplexIntegral_smul]

end Fermionic
end SecondQuantization
