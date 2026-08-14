import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.TwoPointLegEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing

set_option linter.style.header false

/-!
# Vacuum pairing transport for a two-point slot split

For a chosen interaction-slot subset `T`, the complement inherits the ambient increasing order.
This module embeds the fixed-order quartic pairing on that vacuum half into the mixed two-point
pairing of `TwoPointDiagram.ofSlotSplit`.

Everything here is combinatorial: no particle statistics, field-operator realization, Gibbs state,
or physical amplitude enters the construction.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- The increasing inherited order on the quartic complement of a chosen two-point slot set. -/
noncomputable def slotSplitVacuumOrder (T : Finset (Fin n)) :
    QuarticVertexOrder ((Finset.univ : Finset (Fin n)) \ T) :=
  (((Finset.univ : Finset (Fin n)) \ T).orderIsoOfFin rfl).toEquiv

/-- The ambient interaction slot occupied by one local slot in the inherited vacuum order. -/
noncomputable def slotSplitVacuumSlot (T : Finset (Fin n)) :
    Fin ((Finset.univ : Finset (Fin n)) \ T).card → Fin n :=
  fun k => (slotSplitVacuumOrder T k).1

/-- The inherited vacuum-slot map is strictly increasing in ambient interaction-slot order. -/
theorem slotSplitVacuumSlot_strictMono (T : Finset (Fin n)) :
    StrictMono (slotSplitVacuumSlot T) := by
  intro a b hab
  simpa [slotSplitVacuumSlot, slotSplitVacuumOrder] using
    (((Finset.univ : Finset (Fin n)) \ T).orderIsoOfFin rfl).strictMono hab

/-- A fixed-order quartic vacuum leg, viewed as an ambient standard two-point leg, is exactly the
right-leg embedding of the canonical slot split. -/
theorem slotSplitVacuumOrderedLeg_eq_slotSplitRight
    (T : Finset (Fin n))
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p) =
      slotLegSplitting (Finset.subset_univ T)
        (Sum.inr
          (orderedLegToDiagramLeg
            ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) p)) := by
  let q := orderedQuarticLegEquiv
    ((Finset.univ : Finset (Fin n)) \ T).card p
  have hp :
      (orderedQuarticLegEquiv
        ((Finset.univ : Finset (Fin n)) \ T).card).symm q = p :=
    (orderedQuarticLegEquiv
      ((Finset.univ : Finset (Fin n)) \ T).card).symm_apply_apply p
  rw [← hp]
  rcases q with ⟨v, l⟩
  have hordered :
      orderedLegToDiagramLeg
          ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T)
          ((orderedQuarticLegEquiv
            ((Finset.univ : Finset (Fin n)) \ T).card).symm (v, l)) =
        (quarticLegEquiv ((Finset.univ : Finset (Fin n)) \ T)).symm
          (slotSplitVacuumOrder T v, l) := by
    simp [orderedLegToDiagramLeg]
  rw [hordered, slotLegSplitting_right_interaction]
  simp [orderedQuarticLegMapToTwoPointLeg, orderedQuarticLegToTwoPointLeg,
    slotSplitVacuumSlot]

/-- The ambient standard-leg partner on the vacuum side of `ofSlotSplit` is the fixed-order
quartic partner embedded back into the ambient two-point leg enumeration. -/
theorem TwoPointDiagram.ofSlotSplit_atomicLegPartner_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    d.atomicLegPartner (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p) =
      orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T)
        ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner p) := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm.injective
  rw [TwoPointDiagram.atomicLegPartner, Equiv.symm_apply_apply]
  rw [slotSplitVacuumOrderedLeg_eq_slotSplitRight T p,
    slotSplitVacuumOrderedLeg_eq_slotSplitRight T
      ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner p)]
  rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr]
  apply congrArg (fun q => slotLegSplitting (Finset.subset_univ T) (Sum.inr q))
  rw [QuarticDiagram.pairingInOrder, Pairing.relabel_partner, Equiv.apply_symm_apply]

/-- The mixed-order partner on a reassembled diagram is the mixed position of the corresponding
fixed-order quartic vacuum partner. -/
theorem TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    (d.pairingInMixedOrder τ τ' σ).partner
        (mixedTimeOrderedQuarticLegMapPosition
          (slotSplitVacuumSlot T) τ τ' σ p) =
      mixedTimeOrderedQuarticLegMapPosition
        (slotSplitVacuumSlot T) τ τ' σ
        ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner p) := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  change (d.pairingInMixedOrder τ τ' σ).partner
      (mixedTimeOrderedAtomicLegPosition τ τ' σ
        (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p)) = _
  rw [d.pairingInMixedOrder_partner_legPosition,
    TwoPointDiagram.ofSlotSplit_atomicLegPartner_vacuumOrderedLeg T ext vac p]
  rfl

/-- On a strictly ordered inherited vacuum-time assignment, a local fixed-order quartic pair is
normalized if and only if its two endpoints form the corresponding normalized pair in the ambient
mixed two-point pairing. -/
theorem TwoPointDiagram.ofSlotSplit_mem_mixedPairs_vacuumOrderedLeg_iff
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (a b : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    (mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ a,
        mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ b) ∈
      (d.pairingInMixedOrder τ τ' σ).pairs ↔
    (a, b) ∈ (vac.pairingInOrder (slotSplitVacuumOrder T)).pairs := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let E := mixedTimeOrderedQuarticLegMapPosition
    (slotSplitVacuumSlot T) τ τ' σ
  have hE : StrictMono E :=
    mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
      (slotSplitVacuumSlot T) (slotSplitVacuumSlot_strictMono T)
      τ τ' σ hσ
  let e :
      Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card)) ↪o
        Fin (2 * (2 * n + 1)) :=
    OrderEmbedding.ofStrictMono E hE
  change (E a, E b) ∈ (d.pairingInMixedOrder τ τ' σ).pairs ↔
    (a, b) ∈ (vac.pairingInOrder (slotSplitVacuumOrder T)).pairs
  rw [Pairing.mem_pairs_iff, Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mp hab, ?_⟩
    apply e.injective
    change E ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner a) = E b
    calc
      E ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner a) =
          (d.pairingInMixedOrder τ τ' σ).partner (E a) :=
        (TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
          T ext vac τ τ' σ a).symm
      _ = E b := hpartner
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mpr hab, ?_⟩
    rw [TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
      T ext vac τ τ' σ a, hpartner]

/-- Embed a normalized pair of the fixed-order quartic vacuum pairing into the ambient mixed
pairing of `ofSlotSplit`. -/
noncomputable def TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair ↪
      ((TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
        τ τ' σ).NormalizedPair where
  toFun pr :=
    ⟨(mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ pr.1.1,
      mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ pr.1.2),
      (TwoPointDiagram.ofSlotSplit_mem_mixedPairs_vacuumOrderedLeg_iff
        T ext vac τ τ' σ hσ pr.1.1 pr.1.2).2 pr.2⟩
  inj' := by
    intro p q hpq
    have hE : StrictMono (mixedTimeOrderedQuarticLegMapPosition
        (slotSplitVacuumSlot T) τ τ' σ) :=
      mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
        (slotSplitVacuumSlot T) (slotSplitVacuumSlot_strictMono T)
        τ τ' σ hσ
    apply Subtype.ext
    apply Prod.ext
    · apply hE.injective
      exact congrArg (fun z => z.1.1) hpq
    · apply hE.injective
      exact congrArg (fun z => z.1.2) hpq

@[simp]
theorem TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_apply
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ pr).1 =
      (mixedTimeOrderedQuarticLegMapPosition
          (slotSplitVacuumSlot T) τ τ' σ pr.1.1,
        mixedTimeOrderedQuarticLegMapPosition
          (slotSplitVacuumSlot T) τ τ' σ pr.1.2) :=
  rfl

/-- The vacuum normalized-pair embedding preserves and reflects crossings. -/
theorem TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_crosses_iff
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (p q : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    Crosses
        (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
          T ext vac τ τ' σ hσ p).1
        (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
          T ext vac τ τ' σ hσ q).1 ↔
      Crosses p.1 q.1 := by
  let E := mixedTimeOrderedQuarticLegMapPosition
    (slotSplitVacuumSlot T) τ τ' σ
  have hE : StrictMono E :=
    mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
      (slotSplitVacuumSlot T) (slotSplitVacuumSlot_strictMono T)
      τ τ' σ hσ
  simpa [TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding, E] using
    (crosses_map_iff E hE p.1.1 p.1.2 q.1.1 q.1.2)

end Common
end SecondQuantization
