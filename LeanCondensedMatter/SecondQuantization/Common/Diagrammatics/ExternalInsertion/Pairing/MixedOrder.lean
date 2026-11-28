import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.SlotCongr

set_option linter.style.header false

/-!
# Mixed-order pairing transport for external-insertion diagrams

The pairing of any diagram whose internal slots are the full finite slot family can be transported
from fixed flattened-leg positions to mixed-time atomic positions. This construction and its partner
coherence depend only on the diagram pairing and the generic mixed-order position equivalence.
The same module provides full-slot interaction labels and the partner on canonical leg identities.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Slot-indexed interaction labels of an external-insertion diagram. -/
def ExternalInsertionDiagram.vertexLabelSequence {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n))) :
    Fin n → InternalLabel :=
  fun v => d.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- The diagram pairing as a map on canonical external/interaction leg identities. -/
noncomputable def ExternalInsertionDiagram.atomicLegPartner {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (leg : OrderedExternalInsertionLeg E n) : OrderedExternalInsertionLeg E n :=
  externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
    (d.pairing.partner
      ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg))

/-- Transport a diagram pairing from fixed flattened-leg order to mixed-time atomic order. -/
noncomputable def ExternalInsertionDiagram.pairingInMixedOrder {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Pairing (2 * n + E) :=
  d.pairing.transport (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ)

/-- The mixed-order partner of the position selected by a canonical leg is the mixed position of
that leg's diagram partner. -/
theorem ExternalInsertionDiagram.pairingInMixedOrder_partner_legPosition {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    (d.pairingInMixedOrder externalTime σ).partner
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) =
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (d.atomicLegPartner leg) := by
  apply (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).injective
  rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    ← externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    ExternalInsertionDiagram.pairingInMixedOrder,
    PairingOn.transport_partner,
    Equiv.apply_symm_apply,
    externalInsertionMixedTimeAmbientPositionEquiv_legPosition,
    ExternalInsertionDiagram.atomicLegPartner]


/-- Relabel the canonical external and quartic atomic legs by an
arbitrary bijection of interaction vertices. External legs and the four
local leg positions of each vertex are unchanged. -/
noncomputable def externalInsertionOrderedLegSlotCongr
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))) :
    OrderedExternalInsertionLeg E n ≃ OrderedExternalInsertionLeg E n :=
  (Equiv.refl (Fin (2 * E))).sumCongr
    (e.prodCongr (Equiv.refl (Fin 4)))

/-- The actual permutation of mixed-time atomic *positions* induced by
relabeling the interaction vertices and pulling the interaction times
back along the inverse permutation. Equal-time tie breakers may change
this position permutation, so no monotonicity is asserted here. -/
noncomputable def externalInsertionMixedPositionSlotCongr
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + E)) ≃ Fin (2 * (2 * n + E)) :=
  (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).trans
    ((externalInsertionOrderedLegSlotCongr e).trans
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1)).symm)

/-- At arbitrary time assignments, relabeling interaction vertices transports
the full mixed-time pairing along the induced position equivalence. -/
theorem ExternalInsertionDiagram.slotCongr_pairingInMixedOrder_eq_transport
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.slotCongr e).pairingInMixedOrder externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      (d.pairingInMixedOrder externalTime σ).transport
        (externalInsertionMixedPositionSlotCongr e externalTime σ).symm := by
  let σ' := σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1
  let L := externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
  let C := externalInsertionOrderedLegSlotCongr (E := E) e
  let A := externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
  let B := externalInsertionMixedTimeAmbientPositionEquiv externalTime σ'
  let O := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ
  let O' := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ'
  change (d.pairing.transport (L.trans (C.trans L.symm)).symm).transport B =
    (d.pairing.transport A).transport (O.trans (C.trans O'.symm)).symm
  rw [PairingOn.transport_trans, PairingOn.transport_trans]
  apply congrArg (fun p => d.pairing.transport p)
  apply Equiv.ext
  intro i
  apply L.injective
  change L (L.symm (C.symm (L (B i)))) =
    L (A (O.symm (C.symm (O' i))))
  have hA (p : Fin (2 * (2 * n + E))) : L (A p) = O p :=
    externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv externalTime σ p
  have hB (p : Fin (2 * (2 * n + E))) : L (B p) = O' p :=
    externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv externalTime σ' p
  simp only [Equiv.apply_symm_apply, hA, hB]

/-- The vertex permutation on the concrete `Fin n` index induced by an
equivalence of the full interaction slot set. -/
def externalInsertionInteractionSlotPerm
    {n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))) : Equiv.Perm (Fin n) :=
  let u := Equiv.subtypeUnivEquiv (fun v : Fin n => Finset.mem_univ v)
  u.symm.trans (e.trans u)

/-- The canonical-leg transport is precisely the interaction-slot
permutation, extended by the identity on all external legs and the
identity on all four legs of each interaction vertex. -/
theorem externalInsertionOrderedLegSlotCongr_apply_perm
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (leg : OrderedExternalInsertionLeg E n) :
    externalInsertionOrderedLegSlotCongr e leg =
      orderedExternalInsertionLegMap id
        (externalInsertionInteractionSlotPerm e) leg := by
  rcases leg with a | ⟨v, l⟩
  · rfl
  · rfl

/-- On injective interaction-time assignments, the physical
mixed-time position permutation from arbitrary vertex relabeling is
the **identity**. Equal-time coincidences with external insertions
do not change this result, because the tie breaker is external-first.
This bridges sorted-event covariance to actual Wick partner transport. -/
theorem externalInsertionMixedPositionSlotCongr_eq_refl_of_injective
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ)
    (σ : Fin n → ℝ) (hσ : Function.Injective σ) :
    externalInsertionMixedPositionSlotCongr e externalTime σ =
      Equiv.refl (Fin (2 * (2 * n + E))) := by
  let p := externalInsertionInteractionSlotPerm e
  apply Equiv.ext
  intro i
  change (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
      (σ ∘ p.symm)).symm
      (externalInsertionOrderedLegSlotCongr e
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ i)) = i
  apply (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
    (σ ∘ p.symm)).injective
  rw [Equiv.apply_symm_apply, externalInsertionOrderedLegSlotCongr_apply_perm]
  exact (externalInsertionMixedTimeOrderedAtomicLegEquiv_perm_slots
    externalTime σ hσ p i).symm

/-- The physical mixed-time Wick *pairing itself* is unchanged when
interaction slots are relabeled and their time assignment pulled
back, on every injective interaction-time chamber. This is stronger
than partner-intertwining: the pairing lives on exactly the same
mixed-time atomic position type on both sides. -/
theorem ExternalInsertionDiagram.slotCongr_pairingInMixedOrder_eq_of_injective
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ)
    (σ : Fin n → ℝ) (hσ : Function.Injective σ) :
    (d.slotCongr e).pairingInMixedOrder externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      d.pairingInMixedOrder externalTime σ := by
  rw [d.slotCongr_pairingInMixedOrder_eq_transport,
    externalInsertionMixedPositionSlotCongr_eq_refl_of_injective e externalTime σ hσ]
  apply PairingOn.ext
  apply Equiv.ext
  intro i
  simp only [PairingOn.transport_partner, Equiv.refl_symm, Equiv.refl_apply]

end Common
end SecondQuantization
