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
private theorem externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_left
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
  have hLabelComp :
      d.externalLabel ∘ (fun e : Fin (2 * E) => e) = ext.externalLabel := by
    funext e
    exact congrFun hlabel e
  have hTimeComp :
      externalTime ∘ (fun e : Fin (2 * E) => e) = externalTime := by
    funext e
    rfl
  have hmap :=
    externalInsertionMixedTimeOrderedAtomicPairValue_map
      ε β (fun e : Fin (2 * E) => e) f
      d.externalLabel externalTime d.vertexLabelSequence σ a b
  rw [hLabelComp, hTimeComp, hvertices, hlabel] at hmap
  exact hmap


/-- Map local mixed-time positions on the external-support side to the original
flattened positions of the external diagram, using the increasing support-slot order. -/
private noncomputable def externalInsertionLeftMixedToFixedEquiv
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * T.card + E)) ≃ Fin (2 * (2 * T.card + E)) :=
  (externalInsertionMixedTimeOrderedAtomicLegEquiv
    externalTime (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).trans
    ((Equiv.sumCongr
      (Equiv.refl (Fin (2 * E)))
      (((Equiv.subtypeUnivEquiv
        (fun i : Fin T.card => Finset.mem_univ i)).trans
        (T.orderIsoOfFin rfl).toEquiv).prodCongr (Equiv.refl (Fin 4)))).trans
      (externalInsertionLegEquiv E T).symm)

/-- The external-half mixed-position embedding preserves mixed time order, because
the support slots have been enumerated increasingly. -/
private theorem externalInsertionLeftMixedPosition_strictMono
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    StrictMono (fun p : Fin (2 * (2 * T.card + E)) =>
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap (fun e => e)
          (fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)
          (externalInsertionMixedTimeOrderedAtomicLegEquiv
            externalTime (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p))) := by
  apply externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
  · exact strictMono_id
  · exact (T.orderIsoOfFin rfl).strictMono

/-- The mixed-position embedding of the external half is the mixed-order image
of the actual left leg of the assembled slot splitting. -/
private theorem externalInsertionLeftMixedPosition_fixed
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * T.card + E))) :
    let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e) f
            (externalInsertionMixedTimeOrderedAtomicLegEquiv
              externalTime (σ ∘ f) p))) =
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionLeftMixedToFixedEquiv T externalTime σ p)) := by
  let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
  let leg := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime (σ ∘ f) p
  apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).injective
  rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position]
  change orderedExternalInsertionLegMap (fun e => e) f leg =
    externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl ((externalInsertionLegEquiv E T).symm
          ((Equiv.sumCongr (Equiv.refl (Fin (2 * E)))
            (((Equiv.subtypeUnivEquiv
              (fun i : Fin T.card => Finset.mem_univ i)).trans
              (T.orderIsoOfFin rfl).toEquiv).prodCongr
                (Equiv.refl (Fin 4)))) leg))))
  cases leg with
  | inl e =>
      simp [orderedExternalInsertionLegMap,
        externalInsertionSlotLegSplitting_external]
  | inr v =>
      rcases v with ⟨v, l⟩
      simp [orderedExternalInsertionLegMap,
        externalInsertionSlotLegSplitting_left_interaction]

/-- For an actual assembled pairing, every normalized pair on the external-support
side becomes an ambient normalized mixed-time pair with the *same* endpoint order.
Its concrete free-Gibbs contraction is precisely that of the external factor.

No symmetry under reversal of fermionic contraction arguments is used. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_left_normalizedPair
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let localPairing : Pairing (2 * T.card + E) := ext.pairing.transport localFixed
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let embed : Fin (2 * (2 * T.card + E)) → Fin (2 * (2 * n + E)) := fun p =>
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap (fun e => e) f
          (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime (σ ∘ f) p))
    ∀ pr : localPairing.NormalizedPair,
      (embed pr.1.1, embed pr.1.2) ∈ (d.pairingInMixedOrder externalTime σ).pairs ∧
        externalInsertionMixedTimeOrderedAtomicPairValue ε β
          d.externalLabel externalTime d.vertexLabelSequence σ
          (embed pr.1.1) (embed pr.1.2) =
        externalInsertionMixedTimeOrderedAtomicPairValue ε β
          ext.externalLabel externalTime
          (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) (σ ∘ f)
          pr.1.1 pr.1.2 := by
  intro pr
  let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
  let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
  let localPairing : Pairing (2 * T.card + E) := ext.pairing.transport localFixed
  let d : ExternalInsertionWickDiagram Mode E n :=
    ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let embed : Fin (2 * (2 * T.card + E)) → Fin (2 * (2 * n + E)) := fun p =>
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
      (orderedExternalInsertionLegMap (fun e => e) f
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime (σ ∘ f) p))
  have hfixed (p : Fin (2 * (2 * T.card + E))) :
      externalInsertionMixedTimeAmbientPositionEquiv externalTime σ (embed p) =
        externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
          (Sum.inl (localFixed p)) := by
    exact externalInsertionLeftMixedPosition_fixed T externalTime σ p
  have hpartner (p : Fin (2 * (2 * T.card + E))) :
      (d.pairingInMixedOrder externalTime σ).partner (embed p) =
        embed (localPairing.partner p) := by
    apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
    rw [d.mixedTimeAmbientPositionEquiv_partner, hfixed,
      hfixed (localPairing.partner p)]
    change (Pairing.ofSplit
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))
        ext.pairing vac.pairing).partner
          (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
            (Sum.inl (localFixed p))) =
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (localFixed (localPairing.partner p)))
    rw [Pairing.ofSplit_partner_inl]
    change _ = externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
      (Sum.inl (localFixed ((ext.pairing.transport localFixed).partner p)))
    rw [PairingOn.transport_partner, Equiv.apply_symm_apply]
  have hmono : StrictMono embed :=
    externalInsertionLeftMixedPosition_strictMono T externalTime σ
  have hlocalPair :=
    (localPairing.mem_pairs_iff pr.1.1 pr.1.2).mp pr.2
  constructor
  · exact ((d.pairingInMixedOrder externalTime σ).mem_pairs_iff
      (embed pr.1.1) (embed pr.1.2)).mpr
        ⟨hmono hlocalPair.1, by rw [hpartner, hlocalPair.2]⟩
  · let a := externalInsertionMixedTimeOrderedAtomicLegEquiv
      externalTime (σ ∘ f) pr.1.1
    let b := externalInsertionMixedTimeOrderedAtomicLegEquiv
      externalTime (σ ∘ f) pr.1.2
    have hvalue :=
      externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_left
        ε β T ext vac externalTime σ a b
    simpa only [externalInsertionMixedTimeOrderedAtomicLegPosition,
      Equiv.symm_apply_apply] using hvalue

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
