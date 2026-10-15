import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumLegOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Embedding

set_option linter.style.header false

/-!
# Mixed-time image of the slot-split vacuum pairing

The timeless vacuum pairing partner transport belongs to `SlotSplitVacuumLegOrder`.
The normalized-pair embedding into mixed time order additionally assumes `StrictAnti`,
which ensures that the two transported endpoints retain their normalized orientation.
The crossing equivalence is downstream of this order-preserving embedding.

No statistics-dependent signs or thermal weights enter this module.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- Mixed-time atomic leg identities inherit the timeless vacuum-side partner transport. -/
private theorem TwoPointDiagram.ofSlotSplit_atomicLegPartner_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    d.atomicLegPartner (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p) =
      orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T)
        ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner p) := by
  apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm.injective
  rw [TwoPointDiagram.atomicLegPartner, Equiv.symm_apply_apply]
  exact TwoPointDiagram.ofSlotSplit_pairing_partner_vacuumOrderedLeg T ext vac p


/-- The mixed-order partner on a reassembled diagram is the mixed position of the corresponding
fixed-order quartic vacuum partner. -/
private theorem TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
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
        τ τ' σ).NormalizedPair := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  exact
    (vac.pairingInOrder (slotSplitVacuumOrder T)).normalizedPairEmbedding
      (d.pairingInMixedOrder τ τ' σ)
      (slotSplitVacuumMixedOrderEmbedding T τ τ' σ hσ)
      (TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
        T ext vac τ τ' σ)

/-- A mixed normalized pair starting in the vacuum leg embedding has a
preimage in the standalone fixed-order quartic vacuum pairing. -/
theorem TwoPointDiagram.exists_slotSplitVacuumNormalizedPairEmbedding_eq_of_firstEndpoint
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : ((TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
      τ τ' σ).NormalizedPair)
    (hfirst : ∃ p,
      mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ p = pr.1.1) :
    ∃ q, TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ q = pr := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  exact Pairing.exists_normalizedPairEmbedding_eq_of_firstEndpoint
      (vac.pairingInOrder (slotSplitVacuumOrder T))
      (d.pairingInMixedOrder τ τ' σ)
      (slotSplitVacuumMixedOrderEmbedding T τ τ' σ hσ)
      (TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
        T ext vac τ τ' σ) pr hfirst

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
          (slotSplitVacuumSlot T) τ τ' σ pr.1.2) := by
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
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  simpa only [TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding] using
    (vac.pairingInOrder (slotSplitVacuumOrder T)).normalizedPairEmbedding_crosses_iff
      (d.pairingInMixedOrder τ τ' σ)
      (slotSplitVacuumMixedOrderEmbedding T τ τ' σ hσ)
      (TwoPointDiagram.ofSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
        T ext vac τ τ' σ)
      p q


end Common
end SecondQuantization
