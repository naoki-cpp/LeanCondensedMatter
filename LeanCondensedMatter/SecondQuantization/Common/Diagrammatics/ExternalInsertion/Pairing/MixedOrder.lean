import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.SlotCongr

set_option linter.style.header false

/-!
# Mixed-order pairing transport for external-insertion diagrams

The pairing of any diagram whose internal slots are the full finite slot family can be transported
from fixed flattened-leg positions to mixed-time atomic positions. This construction and its partner
coherence depend only on the diagram pairing and the generic mixed-order position equivalence.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

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
  have hpos :
      externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg := by
    apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).injective
    rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
      externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
      Equiv.apply_symm_apply]
  apply (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).injective
  rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    ← externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    ExternalInsertionDiagram.pairingInMixedOrder,
    PairingOn.transport_partner,
    Equiv.apply_symm_apply,
    hpos,
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

/-- The canonical-leg Wick pairing partner is equivariant under any
interaction-vertex permutation. This follows from the *actual*
flattened-leg transport in `slotCongr`, not an abstract, new pairing. -/
theorem ExternalInsertionDiagram.slotCongr_atomicLegPartner
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (leg : OrderedExternalInsertionLeg E n) :
    (d.slotCongr e).atomicLegPartner
        (externalInsertionOrderedLegSlotCongr e leg) =
      externalInsertionOrderedLegSlotCongr e (d.atomicLegPartner leg) := by
  let L := externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
  let P := externalInsertionLegCongr (E := E) e
  let C := externalInsertionOrderedLegSlotCongr (E := E) e
  have hC (p : Fin (2 * (2 *
      (Finset.univ : Finset (Fin n)).card + E))) :
      L (P p) = C (L p) := by
    simp [L, P, C, externalInsertionLegCongr,
      externalInsertionOrderedLegSlotCongr]
  have hCI (a : OrderedExternalInsertionLeg E n) :
      L.symm (C a) = P (L.symm a) := by
    apply L.injective
    rw [L.apply_symm_apply, hC, L.apply_symm_apply]
  change L ((d.slotCongr e).pairing.partner
      (L.symm (C leg))) =
    C (L (d.pairing.partner (L.symm leg)))
  rw [hCI, d.slotCongr_pairing_partner e (L.symm leg),
    hC (d.pairing.partner (L.symm leg))]


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

/-- A canonical atomic leg is sent to its *actual* mixed-time position
after relabeling the interaction slots. -/
theorem externalInsertionMixedPositionSlotCongr_legPosition
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    externalInsertionMixedPositionSlotCongr e externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) =
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1)
        (externalInsertionOrderedLegSlotCongr e leg) := by
  simp [externalInsertionMixedPositionSlotCongr,
    externalInsertionMixedTimeOrderedAtomicLegPosition]

/-- The physical mixed-time Wick pairing partner, at *every* time
assignment (including coincident times), is intertwined by the actual
mixed-time position permutation induced from `slotCongr`.

This preserves the pairing as an involution, but it does not claim
that normalized pair endpoints maintain their increasing order; that
is the additional sign/orientation lemma needed for the integrated
fermionic amplitude. -/
theorem ExternalInsertionDiagram.slotCongr_pairingInMixedOrder_partner
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    ((d.slotCongr e).pairingInMixedOrder externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1)).partner
        (externalInsertionMixedPositionSlotCongr e externalTime σ p) =
      externalInsertionMixedPositionSlotCongr e externalTime σ
        ((d.pairingInMixedOrder externalTime σ).partner p) := by
  let leg := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p
  have hp :
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg = p :=
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm_apply_apply p
  have hpos := externalInsertionMixedPositionSlotCongr_legPosition
    e externalTime σ leg
  rw [← hp, hpos,
    (d.slotCongr e).pairingInMixedOrder_partner_legPosition,
    d.slotCongr_atomicLegPartner,
    d.pairingInMixedOrder_partner_legPosition,
    ← externalInsertionMixedPositionSlotCongr_legPosition]


end Common
end SecondQuantization
