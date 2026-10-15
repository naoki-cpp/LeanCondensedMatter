import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.TwoPointLegEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered

set_option linter.style.header false

/-!
# Vacuum legs and partner transport before mixed time ordering

For a chosen interaction-slot subset `T`, the complement inherits the ambient increasing order.
This module identifies those fixed quartic legs with the right-hand legs of a two-point slot
split and proves compatibility of their pairing partners. It contains no mixed-time ordering
or `StrictAnti` assumption.

The unordered decomposition of all normalized pairs is already provided by the generic
`Pairing.ofSplitNormalizedPairEquiv` for `slotLegSplitting`. It is not duplicated here.
The mixed-time normalized pair embedding and its order/crossing laws live in
`SlotSplitVacuumPairing`.
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

/-- The order embedding of fixed-order vacuum legs into ambient mixed-order leg positions. -/
private noncomputable def slotSplitVacuumMixedOrderEmbedding
    (T : Finset (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card)) ↪o
      Fin (2 * (2 * n + 1)) :=
  OrderEmbedding.ofStrictMono
    (mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ)
    (mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
      (slotSplitVacuumSlot T) (slotSplitVacuumSlot_strictMono T)
      τ τ' σ hσ)

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

/-- Reassembling a slot split intertwines the fixed vacuum pairing partner and the
ambient fixed-leg pairing partner, without choosing an imaginary-time order. -/
theorem TwoPointDiagram.ofSlotSplit_pairing_partner_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    d.pairing.partner
        ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
          (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p)) =
      (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T)
          ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner p)) := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  rw [slotSplitVacuumOrderedLeg_eq_slotSplitRight T p,
    slotSplitVacuumOrderedLeg_eq_slotSplitRight T
      ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner p)]
  rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr]
  apply congrArg (fun q => slotLegSplitting (Finset.subset_univ T) (Sum.inr q))
  rw [QuarticDiagram.pairingInOrder, PairingOn.transport_partner, Equiv.apply_symm_apply]

end Common
end SecondQuantization
