import LeanCondensedMatter.Combinatorics.BinarySplitPermutationSign
import LeanCondensedMatter.Combinatorics.PerfectPairing.SplitNormalizedPairs
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.SlotSplitMixedOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField

set_option linter.style.header false

/-!
# Pairing transport and factorization for external insertions and a vacuum complement

Thermal pair kernels restrict to the external-support and quartic vacuum sectors. Transporting
normalized endpoints preserves their actual orientation; vacuum order hypotheses are explicit.
The resulting contraction products, crossing weights, and pairing evaluations factor with their
inter-sector signs. Analytic shuffle integrals are proved separately.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

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

omit [LinearOrder Mode] [Fintype Mode] in
/-- Express the assembled mixed-time pairing using the external half's own
mixed-time positions. This local reindexing is needed before comparing the
fermionic crossing sign with the mixed atomic-order permutation sign. -/
private theorem externalInsertionOfSlotSplit_pairingInMixedOrder_eq_ofSplit_mixedExternal
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    (ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
        externalTime σ =
      Pairing.ofSplit
        ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (ext.pairing.transport localFixed) (vac.pairingInOrder order) := by
  intro S order localFixed split
  calc
    _ = Pairing.ofSplit split ext.pairing (vac.pairingInOrder order) :=
      ExternalInsertionDiagram.ofSlotSplit_pairingInMixedOrder_eq_ofSplit_orderedVacuum
        T ext vac externalTime σ
    _ = _ := (Pairing.ofSplit_reindex split ext.pairing
      (vac.pairingInOrder order) localFixed
      (Equiv.refl (Fin (2 * (2 * S.card))))).symm

/-- The external half of the reindexed mixed-time slot splitting is strictly
increasing. This does not assert that the original flattened external order is
preserved by the physical time ordering. -/
private theorem externalInsertionLeftMixedPosition_split_strictMono
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    StrictMono (fun p : Fin (2 * (2 * T.card + E)) =>
      ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (Sum.inl p)) := by
  intro S order localFixed split
  have hposition (p : Fin (2 * (2 * T.card + E))) :
      ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
          (Sum.inl p) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e)
            (fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)
            (externalInsertionMixedTimeOrderedAtomicLegEquiv
              externalTime
              (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p)) := by
    apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
    simpa only [split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.refl_apply, Equiv.apply_symm_apply] using
        (externalInsertionLeftMixedPosition_fixed T externalTime σ p).symm
  intro a b hab
  change
    ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (Sum.inl a) <
      ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (Sum.inl b)
  rw [hposition a, hposition b]
  exact (externalInsertionLeftMixedPosition_strictMono T externalTime σ) hab

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
  rw [← hvertices]
  simp only [externalInsertionMixedTimeOrderedAtomicPairValue,
    externalInsertionMixedTimeOrderedAtomicFieldFamily,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    flatVertexLegPairValue]
  rfl

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
  have hsplit :
      (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs, kernel pr.1 pr.2) =
        (∏ pr : ext.pairing.NormalizedPair,
          kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
        ∏ pr : (vac.pairingInOrder order).NormalizedPair,
          kernel (pairEquiv (Sum.inr pr)).1.1 (pairEquiv (Sum.inr pr)).1.2 := by
    have hpairing :
        d.pairingInMixedOrder externalTime σ =
          Pairing.ofSplit split ext.pairing (vac.pairingInOrder order) :=
      ExternalInsertionDiagram.ofSlotSplit_pairingInMixedOrder_eq_ofSplit_orderedVacuum
        T ext vac externalTime σ
    rw [hpairing]
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

/-- If the vacuum-only mixed leg positions preserve their flattened order, their
ambient mixed-time embedding has no reversed vacuum pairs. This directly identifies
the vacuum part of the *physical* free-Gibbs contraction product, leaving the
external-sector and fermionic crossing/order signs separate. -/
theorem externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_flatVacuum_of_localOrder
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
    (StrictMono (fun q : Fin (2 * (2 * S.card)) =>
      externalInsertionMixedTimeOrderedAtomicLegPosition (E := 0)
        (Fin.elim0 : Fin 0 → ℝ) (σ ∘ f)
        (Sum.inr
          (⟨(orderedQuarticLegEquiv S.card q).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv S.card q).2)))) →
    (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs,
        kernel pr.1 pr.2) =
      (∏ pr : ext.pairing.NormalizedPair,
        kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        flatVertexLegPairValue ε β
          (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
          pr.1.1 pr.1.2 := by
  intro S order f d split pairEquiv kernel hlocal
  have hmono :=
    externalInsertionSlotLegSplitting_right_strictMono_of_localOrder
      T externalTime σ hlocal
  apply externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_flatVacuum_of_lt
    ε β T ext vac externalTime σ
  intro pr
  exact hmono ((vac.pairingInOrder order).pairs_normalized pr.2)

/-- On a strictly antitone vacuum time chamber, the actual assembled
mixed-time Wick contraction product has the standalone quartic vacuum kernel
factor. No endpoint-exchange symmetry of the fermionic contraction is used. -/
theorem externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_flatVacuum_of_strictAnti
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
    StrictAnti (σ ∘ f) →
    (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs,
        kernel pr.1 pr.2) =
      (∏ pr : ext.pairing.NormalizedPair,
        kernel (pairEquiv (Sum.inl pr)).1.1 (pairEquiv (Sum.inl pr)).1.2) *
      ∏ pr : (vac.pairingInOrder order).NormalizedPair,
        flatVertexLegPairValue ε β
          (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
          pr.1.1 pr.1.2 := by
  intro S order f d split pairEquiv kernel htime
  apply externalInsertionOfSlotSplit_prod_mixedPairContractions_eq_left_mul_flatVacuum_of_localOrder
    ε β T ext vac externalTime σ
  exact externalInsertionMixedTimeOrderedAtomicLegPosition_zero_strictMono_of_strictAnti
    (σ ∘ f) htime

omit [LinearOrder Mode] [Fintype Mode] in
/-- The relative permutation between the fixed and mixed atomic support/vacuum
splittings carries the full mixed-time ordering sign and the actual
external-support local reordering sign. No order-preservation assumption
is made about the external support in its original flattened order.
The vacuum local order is the identity in this comparison. -/
theorem externalInsertionMixedSplit_relativePerm_sign_eq_local_mul_global
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let fixedSplit :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (finCongr (by simp)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
      Equiv.Perm.sign
          (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))) *
        Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) := by
  intro S order localFixed fixedSplit split mixedSplit
  let localPerm : Equiv.Perm
      (Fin (2 * (2 * T.card + E)) ⊕ Fin (2 * (2 * S.card))) :=
    Equiv.sumCongr localFixed (Equiv.refl _)
  let globalPerm : Equiv.Perm (Fin (2 * (2 * n + E))) :=
    externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ
  have hsplit : split = fixedSplit.trans globalPerm := by
    apply Equiv.ext
    intro p
    rfl
  have hrelative :
      fixedSplit.symm.trans mixedSplit =
        (fixedSplit.symm.trans (localPerm.trans fixedSplit)).trans globalPerm := by
    rw [show mixedSplit = localPerm.trans split from rfl, hsplit]
    apply Equiv.ext
    intro p
    rfl
  have hassoc :
      fixedSplit.symm.trans (localPerm.trans fixedSplit) =
        (fixedSplit.symm.trans localPerm).trans fixedSplit := by
    apply Equiv.ext
    intro p
    rfl
  rw [hrelative, Equiv.Perm.sign_trans, hassoc,
    Equiv.Perm.sign_symm_trans_trans]
  exact mul_comm _ _

omit [LinearOrder Mode] [Fintype Mode] in
/-- The relative fixed/mixed support split sign is determined by the two
inter-sector inversion counts on strictly antitone vacuum time chambers.
Both fixed-sector embeddings are now shown to preserve the canonical flattened
order; the parity of the fixed inter-sector inversion count remains separate. -/
theorem externalInsertionMixedSplit_relativePerm_sign_eq_inversionCounts
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let fixedSplit :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (finCongr (by simp)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    StrictAnti (σ ∘ f) →
    Equiv.Perm.sign (fixedSplit.symm.trans mixedSplit) =
      (-1 : ℤˣ) ^
        ((∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if fixedSplit (Sum.inr j) < fixedSplit (Sum.inl i) then 1 else 0) +
          (∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0)) := by
  intro S order f localFixed fixedSplit split mixedSplit htime
  have hfixedLeft : StrictMono
      (fun i : Fin (2 * (2 * T.card + E)) => fixedSplit (Sum.inl i)) := by
    intro a b hab
    have hleft :=
      externalInsertionSlotLegSplitting_left_strictMono (E := E) T hab
    change (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl a))).val <
      (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl b))).val
    simpa only [Fin.val_cast, Fin.lt_def] using hleft
  have hfixedRight : StrictMono
      (fun j : Fin (2 * (2 * S.card)) => fixedSplit (Sum.inr j)) := by
    intro a b hab
    have hright :=
      externalInsertionSlotLegSplitting_orderedRight_strictMono (E := E) T hab
    change (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order a)))).val <
      (Fin.cast (by simp)
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order b)))).val
    simpa only [Fin.val_cast, Fin.lt_def] using hright
  have hmixedLeft : StrictMono
      (fun i : Fin (2 * (2 * T.card + E)) => mixedSplit (Sum.inl i)) :=
    externalInsertionLeftMixedPosition_split_strictMono T externalTime σ
  have hright0 :=
    externalInsertionSlotLegSplitting_right_strictMono_of_localOrder T externalTime σ
      (externalInsertionMixedTimeOrderedAtomicLegPosition_zero_strictMono_of_strictAnti
        (σ ∘ f) htime)
  have hmixedRight : StrictMono
      (fun j : Fin (2 * (2 * S.card)) => mixedSplit (Sum.inr j)) := by
    simpa only [mixedSplit, split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.refl_apply] using hright0
  exact sign_relative_binarySplittings_eq_inversionCounts
    fixedSplit mixedSplit hfixedLeft hfixedRight hmixedLeft hmixedRight

omit [LinearOrder Mode] [Fintype Mode] in
/-- On a strictly antitone vacuum chamber, the actual mixed-time fermionic
crossing weight splits into the external mixed-order weight, the ordered vacuum
weight, and the sign of the inter-sector atomic-position inversions.
The left sector is explicitly reordered into standalone mixed-time positions;
its original flattened position order is not assumed to be preserved. -/
theorem externalInsertionOfSlotSplit_mixedPairingWeight_eq_positionInversions_mul_of_strictAnti
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    let localPairing : Pairing (2 * T.card + E) := ext.pairing.transport localFixed
    StrictAnti (σ ∘ f) →
      ((ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
          externalTime σ).weight Common.Statistics.fermion =
        (Common.Statistics.fermion.zetaInt : ℂ) ^
          (∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0) *
          (localPairing.weight Common.Statistics.fermion *
            (vac.pairingInOrder order).weight Common.Statistics.fermion) := by
  intro S order f localFixed split mixedSplit localPairing htime
  have hleft :
      StrictMono (fun i : Fin (2 * (2 * T.card + E)) =>
        mixedSplit (Sum.inl i)) :=
    externalInsertionLeftMixedPosition_split_strictMono T externalTime σ
  have hright0 :=
    externalInsertionSlotLegSplitting_right_strictMono_of_localOrder T externalTime σ
      (externalInsertionMixedTimeOrderedAtomicLegPosition_zero_strictMono_of_strictAnti
        (σ ∘ f) htime)
  have hright :
      StrictMono (fun j : Fin (2 * (2 * S.card)) =>
        mixedSplit (Sum.inr j)) := by
    simpa only [mixedSplit, split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.refl_apply] using hright0
  rw [externalInsertionOfSlotSplit_pairingInMixedOrder_eq_ofSplit_mixedExternal
    T ext vac externalTime σ]
  exact Common.BlochDeDominicis.Pairing.weight_ofSplit_eq_positionInversions_mul
    Common.Statistics.fermion mixedSplit
    localPairing (vac.pairingInOrder order) hleft hright

/-- The actual physical mixed-time pairing evaluation splits into its standalone
external-support and ordered-vacuum evaluations, up to the fermionic sign of
the right-before-left inter-sector positions. The external pairing is first
transported into its own mixed-time atomic order; the vacuum vertices are in
a strictly antitone chamber. Neither kernel is assumed symmetric under
reversal of the pair endpoints. -/
theorem externalInsertionOfSlotSplit_mixedPairingEvaluation_eq_positionInversions_mul_of_strictAnti
    (ε : Mode → ℝ) (β : ℝ) {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let fT : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let mixedSplit :=
      (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split
    let localPairing : Pairing (2 * T.card + E) := ext.pairing.transport localFixed
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let kernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
    let leftKernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      ext.externalLabel externalTime
      (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) (σ ∘ fT)
    let rightKernel := flatVertexLegPairValue ε β
      (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
    StrictAnti (σ ∘ f) →
      (d.pairingInMixedOrder externalTime σ).evaluation
          ((d.pairingInMixedOrder externalTime σ).weight Common.Statistics.fermion)
          kernel =
        (Common.Statistics.fermion.zetaInt : ℂ) ^
          (∑ i : Fin (2 * (2 * T.card + E)),
            ∑ j : Fin (2 * (2 * S.card)),
              if mixedSplit (Sum.inr j) < mixedSplit (Sum.inl i) then 1 else 0) *
          (localPairing.evaluation (localPairing.weight Common.Statistics.fermion)
              leftKernel *
            (vac.pairingInOrder order).evaluation
              ((vac.pairingInOrder order).weight Common.Statistics.fermion)
              rightKernel) := by
  intro S order f fT localFixed split mixedSplit localPairing d kernel
    leftKernel rightKernel htime
  let pairEquiv := Pairing.ofSplitNormalizedPairEquiv
    mixedSplit localPairing (vac.pairingInOrder order)
  have hleftMono :
      StrictMono (fun p : Fin (2 * (2 * T.card + E)) =>
        mixedSplit (Sum.inl p)) :=
    externalInsertionLeftMixedPosition_split_strictMono T externalTime σ
  have hright0 :=
    externalInsertionSlotLegSplitting_right_strictMono_of_localOrder T externalTime σ
      (externalInsertionMixedTimeOrderedAtomicLegPosition_zero_strictMono_of_strictAnti
        (σ ∘ f) htime)
  have hrightMono :
      StrictMono (fun q : Fin (2 * (2 * S.card)) =>
        mixedSplit (Sum.inr q)) := by
    simpa only [mixedSplit, split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.refl_apply] using hright0
  have hposLeft (p : Fin (2 * (2 * T.card + E))) :
      mixedSplit (Sum.inl p) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e) fT
            (externalInsertionMixedTimeOrderedAtomicLegEquiv
              externalTime (σ ∘ fT) p)) := by
    apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
    simpa only [mixedSplit, split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.refl_apply, Equiv.apply_symm_apply] using
        (externalInsertionLeftMixedPosition_fixed T externalTime σ p).symm
  have hposRight (q : Fin (2 * (2 * S.card))) :
      mixedSplit (Sum.inr q) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (Sum.inr
            (⟨(order (orderedQuarticLegEquiv S.card q).1).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv S.card q).2)) := by
    simpa only [mixedSplit, split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.refl_apply] using
        (externalInsertionSlotLegSplitting_right_orderedMixedPosition
          T externalTime σ q)
  have hleft : ∀ pr : localPairing.NormalizedPair,
      kernel (pairEquiv (Sum.inl pr)).1.1
        (pairEquiv (Sum.inl pr)).1.2 =
      leftKernel pr.1.1 pr.1.2 := by
    intro pr
    have hpair :=
      Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt
        mixedSplit localPairing (vac.pairingInOrder order) (Sum.inl pr)
        (hleftMono (localPairing.pairs_normalized pr.2))
    change kernel (pairEquiv (Sum.inl pr)).1.1
        (pairEquiv (Sum.inl pr)).1.2 = leftKernel pr.1.1 pr.1.2
    rw [hpair]
    change kernel (mixedSplit (Sum.inl pr.1.1))
        (mixedSplit (Sum.inl pr.1.2)) = leftKernel pr.1.1 pr.1.2
    rw [hposLeft, hposLeft]
    exact (externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_left_normalizedPair
      ε β T ext vac externalTime σ pr).2
  have hright : ∀ pr : (vac.pairingInOrder order).NormalizedPair,
      kernel (pairEquiv (Sum.inr pr)).1.1
        (pairEquiv (Sum.inr pr)).1.2 =
      rightKernel pr.1.1 pr.1.2 := by
    intro pr
    have hpair :=
      Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt
        mixedSplit localPairing (vac.pairingInOrder order) (Sum.inr pr)
        (hrightMono ((vac.pairingInOrder order).pairs_normalized pr.2))
    change kernel (pairEquiv (Sum.inr pr)).1.1
        (pairEquiv (Sum.inr pr)).1.2 = rightKernel pr.1.1 pr.1.2
    rw [hpair]
    change kernel (mixedSplit (Sum.inr pr.1.1))
        (mixedSplit (Sum.inr pr.1.2)) = rightKernel pr.1.1 pr.1.2
    rw [hposRight, hposRight]
    exact externalInsertionMixedTimeOrderedAtomicPairValue_ofSlotSplit_right_locality
      ε β T ext vac externalTime σ pr.1.1 pr.1.2
  have hpairing :
      d.pairingInMixedOrder externalTime σ =
        Pairing.ofSplit mixedSplit localPairing (vac.pairingInOrder order) :=
    externalInsertionOfSlotSplit_pairingInMixedOrder_eq_ofSplit_mixedExternal
      T ext vac externalTime σ
  rw [hpairing]
  exact Common.BlochDeDominicis.Pairing.evaluation_ofSplit_eq_positionInversions_mul
    Common.Statistics.fermion mixedSplit localPairing (vac.pairingInOrder order)
    kernel leftKernel rightKernel hleftMono hrightMono hleft hright

end Fermionic
end SecondQuantization
