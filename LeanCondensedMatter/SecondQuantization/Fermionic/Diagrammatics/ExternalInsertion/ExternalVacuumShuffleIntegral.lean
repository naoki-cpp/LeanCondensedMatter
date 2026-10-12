import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Combinatorics.SlotShuffle
import LeanCondensedMatter.Combinatorics.PerfectPairing.SplitNormalizedPairs
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
      change Sum.inl e =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n)))
          (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
            (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inl e))))
      rw [externalInsertionSlotLegSplitting_external, Equiv.apply_symm_apply]
  | inr v =>
      rcases v with ⟨v, l⟩
      change Sum.inr (⟨f v.1, Finset.mem_univ _⟩, l) =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n)))
          (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
            (Sum.inl ((externalInsertionLegEquiv E T).symm
              (Sum.inr ((T.orderIsoOfFin rfl v.1), l)))))
      rw [externalInsertionSlotLegSplitting_left_interaction, Equiv.apply_symm_apply]

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
    let localFixed :=
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime (σ ∘ f)).trans
        ((Equiv.sumCongr
          (Equiv.refl (Fin (2 * E)))
          (((Equiv.subtypeUnivEquiv
            (fun i : Fin T.card => Finset.mem_univ i)).trans
            (T.orderIsoOfFin rfl).toEquiv).prodCongr (Equiv.refl (Fin 4)))).trans
          (externalInsertionLegEquiv E T).symm)
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
  intro f localFixed localPairing d embed pr
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
    have ha :
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime (σ ∘ f) a =
          pr.1.1 := by
      exact (externalInsertionMixedTimeOrderedAtomicLegEquiv
        externalTime (σ ∘ f)).symm_apply_apply pr.1.1
    have hb :
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime (σ ∘ f) b =
          pr.1.2 := by
      exact (externalInsertionMixedTimeOrderedAtomicLegEquiv
        externalTime (σ ∘ f)).symm_apply_apply pr.1.2
    dsimp only at hvalue
    rw [ha, hb] at hvalue
    exact hvalue

/-- The actual quartic vacuum half of an assembled external-insertion diagram has
the standalone free-Gibbs pair kernel when its vertex slots are reindexed into the
ambient diagram. The arguments retain their given order; normalization of ambient
pairs after reassembly is a separate assertion. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_locality
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
        d.externalLabel externalTime d.vertexLabelSequence σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
            (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) f
            (Sum.inr (⟨(orderedQuarticLegEquiv S.card a).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv S.card a).2))))
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
            (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) f
            (Sum.inr (⟨(orderedQuarticLegEquiv S.card b).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv S.card b).2)))) =
      flatVertexLegPairValue ε β
        (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v))
        (σ ∘ f) a b := by
  intro S f d
  have hvertices :
      d.vertexLabelSequence ∘ f =
        (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) := by
    funext v
    let w := S.orderIsoOfFin rfl v
    have hw : (w.1 : Fin n) ∉ T := (Finset.mem_sdiff.mp w.2).2
    change
      (ExternalInsertionDiagram.ofSlotSplit
        (Finset.subset_univ T) ext vac).vertexLabel
        ⟨w.1, Finset.mem_univ _⟩ = vac.vertexLabel w
    rw [ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem
      (Finset.subset_univ T) ext vac
      ⟨w.1, Finset.mem_univ _⟩ hw]
  have hkernel :=
    externalInsertionMixedTimeOrderedAtomicPairValue_quartic_map
      ε β f d.externalLabel externalTime d.vertexLabelSequence σ a b
  rw [hvertices] at hkernel
  exact hkernel

/-- The vacuum-side ambient normalized contraction agrees with its standalone
quartic kernel whenever the transported endpoints retain their order.

This hypothesis is necessary: arbitrary mixed-time slot permutations can reverse
a pair, and a fermionic contraction kernel is not symmetric in its arguments. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_normalizedPair_of_lt
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let splitting :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let pairEquiv := Pairing.ofSplitNormalizedPairEquiv
      splitting ext.pairing (vac.pairingInOrder order)
    let kernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
    ∀ pr : (vac.pairingInOrder order).NormalizedPair,
      splitting (Sum.inr pr.1.1) < splitting (Sum.inr pr.1.2) →
      kernel (pairEquiv (Sum.inr pr)).1.1 (pairEquiv (Sum.inr pr)).1.2 =
        flatVertexLegPairValue ε β
          (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
          pr.1.1 pr.1.2 := by
  intro S order f d splitting pairEquiv kernel pr horder
  have hpair :
      (pairEquiv (Sum.inr pr)).1 =
        (splitting (Sum.inr pr.1.1), splitting (Sum.inr pr.1.2)) :=
    Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt
      splitting ext.pairing (vac.pairingInOrder order) (Sum.inr pr) horder
  have hpos (q : Fin (2 * (2 * S.card))) :
      splitting (Sum.inr q) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (Sum.inr
            (⟨(order (orderedQuarticLegEquiv S.card q).1).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv S.card q).2)) :=
    externalInsertionSlotLegSplitting_right_orderedMixedPosition T externalTime σ q
  have hkernel :=
    externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_locality
      ε β T ext vac externalTime σ pr.1.1 pr.1.2
  change kernel
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (Sum.inr
          (⟨(order (orderedQuarticLegEquiv S.card pr.1.1).1).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv S.card pr.1.1).2)))
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (Sum.inr
          (⟨(order (orderedQuarticLegEquiv S.card pr.1.2).1).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv S.card pr.1.2).2))) =
      flatVertexLegPairValue ε β
        (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v))
        (σ ∘ f) pr.1.1 pr.1.2 at hkernel
  rw [hpair, hpos, hpos]
  exact hkernel

/-- The vacuum contraction of an ambient normalized pair is the standalone
quartic contraction in the order actually induced by the mixed-time splitting.
A reversed pair evaluates at reversed arguments, not at a presumed symmetric
fermionic kernel. No order hypothesis is needed. -/
theorem externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_normalizedPair
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let splitting :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let pairEquiv := Pairing.ofSplitNormalizedPairEquiv
      splitting ext.pairing (vac.pairingInOrder order)
    let kernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
    ∀ pr : (vac.pairingInOrder order).NormalizedPair,
      kernel (pairEquiv (Sum.inr pr)).1.1 (pairEquiv (Sum.inr pr)).1.2 =
        if splitting (Sum.inr pr.1.1) < splitting (Sum.inr pr.1.2) then
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.1 pr.1.2
        else
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.2 pr.1.1 := by
  intro S order f d splitting pairEquiv kernel pr
  have hpos (q : Fin (2 * (2 * S.card))) :
      splitting (Sum.inr q) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (Sum.inr
            (⟨(order (orderedQuarticLegEquiv S.card q).1).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv S.card q).2)) :=
    externalInsertionSlotLegSplitting_right_orderedMixedPosition T externalTime σ q
  by_cases horder : splitting (Sum.inr pr.1.1) < splitting (Sum.inr pr.1.2)
  · simp only [horder, ↓reduceIte]
    exact externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_normalizedPair_of_lt
      ε β T ext vac externalTime σ pr horder
  · simp only [horder, ↓reduceIte]
    have hpair :=
      Pairing.ofSplitNormalizedPairEquiv_pair_eq_or_swap
        splitting ext.pairing (vac.pairingInOrder order) (Sum.inr pr)
    rcases hpair with hnormal | hreversed
    · have hnormalized :=
        (Pairing.ofSplit splitting ext.pairing
          (vac.pairingInOrder order)).pairs_normalized
          (pairEquiv (Sum.inr pr)).2
      rw [hnormal] at hnormalized
      exact (horder hnormalized).elim
    · rw [hreversed]
      dsimp only
      rw [hpos, hpos]
      exact externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_locality
        ε β T ext vac externalTime σ pr.1.2 pr.1.1

/-- Evaluating all vacuum-side Wick contractions of an assembled external-insertion
diagram on its inherited quartic pairing gives the standalone quartic pairing
evaluation, including its fermionic crossing weight.

Here both products use the *vacuum pairing's* normalized endpoints. Identifying these
with the ambient mixed-order pairing's normalized endpoints remains a separate step. -/
theorem externalInsertionOfSlotSplit_vacuumPairingEvaluation_eq_flatVertex
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    vac.pairing.evaluation (vac.pairing.weight Common.Statistics.fermion)
      (fun a b =>
        externalInsertionMixedTimeOrderedAtomicPairValue ε β
          d.externalLabel externalTime d.vertexLabelSequence σ
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
            (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
              (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) f
              (Sum.inr (⟨(orderedQuarticLegEquiv S.card a).1, Finset.mem_univ _⟩,
                (orderedQuarticLegEquiv S.card a).2))))
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
            (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
              (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) f
              (Sum.inr (⟨(orderedQuarticLegEquiv S.card b).1, Finset.mem_univ _⟩,
                (orderedQuarticLegEquiv S.card b).2))))) =
      flatVertexLegPairingEvaluation ε β
        (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v))
        (σ ∘ f) vac.pairing := by
  intro S f d
  change vac.pairing.evaluation (vac.pairing.weight Common.Statistics.fermion) _ =
    vac.pairing.evaluation (vac.pairing.weight Common.Statistics.fermion)
      (flatVertexLegPairValue ε β
        (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f))
  have hkernel :
      (fun a b : Fin (2 * (2 * S.card)) =>
        externalInsertionMixedTimeOrderedAtomicPairValue ε β
          d.externalLabel externalTime d.vertexLabelSequence σ
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
            (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
              (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) f
              (Sum.inr (⟨(orderedQuarticLegEquiv S.card a).1, Finset.mem_univ _⟩,
                (orderedQuarticLegEquiv S.card a).2))))
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
            (orderedExternalInsertionLegMap (E₁ := 0) (E₂ := E)
              (Fin.elim0 : Fin (2 * 0) → Fin (2 * E)) f
              (Sum.inr (⟨(orderedQuarticLegEquiv S.card b).1, Finset.mem_univ _⟩,
                (orderedQuarticLegEquiv S.card b).2))))) =
        flatVertexLegPairValue ε β
          (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f) := by
    funext a b
    exact externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_locality
      ε β T ext vac externalTime σ a b
  rw [hkernel]

/-- The contraction product of an assembled arbitrary-external diagram splits
into products on the external-side pairing and the vacuum pairing transported to
the *increasing complementary vertex order*.

Both sides use ambient-normalized endpoints determined by the binary splitting
equivalence, so no symmetry of the fermionic kernel under endpoint reversal is
assumed. The local-kernel comparisons remain separate. -/
theorem externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_split
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let pairEquiv := Pairing.ofSplitNormalizedPairEquiv
      split ext.pairing (vac.pairingInOrder order)
    let kernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
    (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs,
        kernel pr.1 pr.2) =
      (∏ pr : ext.pairing.NormalizedPair,
        kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        kernel (pairEquiv (Sum.inr pr)).1.1 (pairEquiv (Sum.inr pr)).1.2 := by
  intro S order d split pairEquiv kernel
  have hsplit :
      d.pairingInMixedOrder externalTime σ =
        Pairing.ofSplit split ext.pairing (vac.pairingInOrder order) :=
    ExternalInsertionDiagram.ofSlotSplit_pairingInMixedOrder_eq_ofSplit_orderedVacuum
      T ext vac externalTime σ
  rw [hsplit]
  let pairing := Pairing.ofSplit split ext.pairing (vac.pairingInOrder order)
  change (∏ pr ∈ pairing.pairs, kernel pr.1 pr.2) =
    (∏ pr : ext.pairing.NormalizedPair,
      kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        kernel (pairEquiv (Sum.inr pr)).1.1 (pairEquiv (Sum.inr pr)).1.2
  calc
    (∏ pr ∈ pairing.pairs, kernel pr.1 pr.2) =
        ∏ pr : pairing.NormalizedPair, kernel pr.1.1 pr.1.2 :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ pr : ext.pairing.NormalizedPair ⊕
        (vac.pairingInOrder order).NormalizedPair,
          kernel (pairEquiv pr).1.1 (pairEquiv pr).1.2 :=
      (Equiv.prod_comp pairEquiv (fun pr => kernel pr.1.1 pr.1.2)).symm
    _ = _ := Fintype.prod_sum_type _

/-- Factor the actual ambient mixed-time contraction product without an
endpoint-order assumption. Vacuum factors use the standalone physical kernel
with the orientation induced by the split; the external factors still require
their own mixed-order identification. -/
theorem externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_orientedVacuum
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let pairEquiv := Pairing.ofSplitNormalizedPairEquiv
      split ext.pairing (vac.pairingInOrder order)
    let kernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
    (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs,
        kernel pr.1 pr.2) =
      (∏ pr : ext.pairing.NormalizedPair,
        kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        if split (Sum.inr pr.1.1) < split (Sum.inr pr.1.2) then
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.1 pr.1.2
        else
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.2 pr.1.1 := by
  intro S order f d split pairEquiv kernel
  have hvac :
      (∏ pr : (vac.pairingInOrder order).NormalizedPair,
        kernel (pairEquiv (Sum.inr pr)).1.1 (pairEquiv (Sum.inr pr)).1.2) =
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        if split (Sum.inr pr.1.1) < split (Sum.inr pr.1.2) then
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.1 pr.1.2
        else
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.2 pr.1.1 := by
    apply Fintype.prod_congr
    intro pr
    exact externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_normalizedPair
      ε β T ext vac externalTime σ pr
  have hsplit :=
    externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_split
      ε β T ext vac externalTime σ
  exact hsplit.trans
    (congrArg
      (fun z : ℂ =>
        (∏ pr : ext.pairing.NormalizedPair,
          kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) * z)
      hvac)

/-- When every transported vacuum pair retains its endpoint order, the
vacuum factor in the actual assembled mixed-time Wick contraction product is
the standalone quartic free-Gibbs contraction product.

The external factor still uses ambient-normalized endpoints. If a vacuum pair
is reversed by the mixed-time ordering, this theorem does not assume the
fermionic contraction is invariant under that reversal. -/
theorem externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_flatVacuum_of_lt
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let pairEquiv := Pairing.ofSplitNormalizedPairEquiv
      split ext.pairing (vac.pairingInOrder order)
    let kernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
    (∀ pr : (vac.pairingInOrder order).NormalizedPair,
      split (Sum.inr pr.1.1) < split (Sum.inr pr.1.2)) →
    (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs,
        kernel pr.1 pr.2) =
      (∏ pr : ext.pairing.NormalizedPair,
        kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        flatVertexLegPairValue ε β
          (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
          pr.1.1 pr.1.2 := by

  intro S order f d split pairEquiv kernel horder
  have h :=
    externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_orientedVacuum
      ε β T ext vac externalTime σ
  calc
    _ = _ := h
    _ = _ := by
      congr 1
      apply Fintype.prod_congr
      intro pr
      change
        (if split (Sum.inr pr.1.1) < split (Sum.inr pr.1.2) then
            flatVertexLegPairValue ε β
              (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
              pr.1.1 pr.1.2
          else
            flatVertexLegPairValue ε β
              (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
              pr.1.2 pr.1.1) =
          flatVertexLegPairValue ε β
            (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
            pr.1.1 pr.1.2
      simp only [horder pr, ↓reduceIte]

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
