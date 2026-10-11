import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Combinatorics.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SlotLegSplitting

set_option linter.style.header false

/-!
# Binary shuffle integral for arbitrary external insertions and vacuum data

The fixed external-insertion Dyson integrand is measurably locally bounded. Pairing it with the
continuous fixed-order quartic vacuum integrand allows the general binary ordered-simplex shuffle
identity to separate their integrated contributions. This is the analytic product theorem needed
after the external-support fibers have been reindexed by slot shuffles.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The free-Gibbs contraction of two quartic interaction legs embedded in the
arbitrary-external mixed-time leg order agrees with the canonical vacuum Dyson
pair kernel. Both sides use the same ordered endpoints; this does not identify
the orientation of an ambient normalized pair after an external/vacuum shuffle. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_quartic
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ}
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (a b : Fin (2 * (2 * n))) :
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
        externalLabel externalTime q σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (Sum.inr (⟨(orderedQuarticLegEquiv n a).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv n a).2)))
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (Sum.inr (⟨(orderedQuarticLegEquiv n b).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv n b).2))) =
      flatVertexLegPairValue ε β q σ a b := by
  simp only [externalInsertionMixedTimeOrderedAtomicPairValue,
    externalInsertionMixedTimeOrderedAtomicFieldFamily,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    flatVertexLegPairValue]
  rfl

/-- The quartic vacuum pair kernel remains unchanged after embedding its
interaction slots into an ambient arbitrary-external mixed-time diagram. In
particular this applies to the vacuum half of a binary slot shuffle; endpoint
orientation is kept explicit rather than quotienting by pair reversal. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_quartic_map
    (ε : Mode → ℝ) (β : ℝ) {E m n : ℕ}
    (fInteraction : Fin m → Fin n)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (a b : Fin (2 * (2 * m))) :
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
        externalLabel externalTime q σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
            (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) fInteraction
            (Sum.inr (⟨(orderedQuarticLegEquiv m a).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv m a).2))))
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
            (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) fInteraction
            (Sum.inr (⟨(orderedQuarticLegEquiv m b).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv m b).2)))) =
      flatVertexLegPairValue ε β (q ∘ fInteraction) (σ ∘ fInteraction) a b := by
  simp only [externalInsertionMixedTimeOrderedAtomicPairValue,
    externalInsertionMixedTimeOrderedAtomicFieldFamily,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    flatVertexLegPairValue]
  rfl

/-- The concrete mixed-time free-Gibbs contraction on the external half of an assembled
slot split equals the contraction of its standalone external half. This compares the ordered
endpoints, before normalized pair orientation and crossing signs are transported. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_left
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : OrderedExternalInsertionLeg E T.card) :
    let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
        d.externalLabel externalTime d.vertexLabelSequence σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e) f a))
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e) f b)) =
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
        ext.externalLabel externalTime
        (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) (σ ∘ f)
        (externalInsertionMixedTimeOrderedAtomicLegPosition
          externalTime (σ ∘ f) a)
        (externalInsertionMixedTimeOrderedAtomicLegPosition
          externalTime (σ ∘ f) b) := by
  let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
  let d : ExternalInsertionWickDiagram Mode E n :=
    ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  have hlabel : d.externalLabel = ext.externalLabel := rfl
  have hvertices :
      d.vertexLabelSequence ∘ f =
        (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) := by
    funext v
    change (ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).vertexLabel
        ⟨(T.orderIsoOfFin rfl v).1, Finset.mem_univ _⟩ =
      ext.vertexLabel (T.orderIsoOfFin rfl v)
    rw [ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem
      (Finset.subset_univ T) ext vac
      ⟨(T.orderIsoOfFin rfl v).1, Finset.mem_univ _⟩
      (T.orderIsoOfFin rfl v).2]
    rfl
  change externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap (fun e => e) f a))
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap (fun e => e) f b)) =
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
      ext.externalLabel externalTime
      (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) (σ ∘ f)
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime (σ ∘ f) a)
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime (σ ∘ f) b)
  simpa only [Function.comp_id, hlabel, hvertices] using
    (externalInsertionMixedTimeOrderedAtomicPairValue_map
      ε β (fun e : Fin (2 * E) => e) f
      d.externalLabel externalTime d.vertexLabelSequence σ a b)


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
          (fun σ => (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
            flatVertexLegPairingEvaluation ε β x.1 σ x.2))) =
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
          (fun σ => (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
            flatVertexLegPairingEvaluation ε β x.1 σ x.2) :=
      BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
        m k β
        (fun σ => ext.dysonFixedTimeAmplitude ε β g externalTime σ)
        (fun σ => (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
          flatVertexLegPairingEvaluation ε β x.1 σ x.2) hext hvac
    _ = _ := by
      rw [ext.orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g externalTime,
        intervalIntegral.orderedSimplexIntegral_smul]

end Fermionic
end SecondQuantization
