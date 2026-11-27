import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportStandardization

set_option linter.style.header false

/-!
# Component-local mixed-order external-insertion data

A restricted external-insertion component retains its interaction vertices as a subset of the
ambient slots. Standalone component diagrams use consecutive `Fin m` interaction slots. This module supplies the canonical increasing reindexing needed to apply the component diagram
data to one connected component, together with the induced local external and interaction times.
It identifies local canonical legs with their ambient counterparts and constructs the induced
mixed-position embeddings and order-preserving family shuffle. The normalized-pair equivalence
belongs to `Pairing.ComponentMixedPairEquiv`; timed-field and thermal-kernel locality belong to
Fermionic consumers.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- Reindex one connected component by consecutive interaction slots while preserving the canonical
component external order and restricted pairing. -/
noncomputable def ExternalInsertionDiagram.componentOrderedDiagram {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts) :
    ExternalInsertionDiagram ExternalLabel InternalLabel (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card
      Finset.univ :=
  (d.restrictComponent B).slotCongr
    (Combinatorics.standardSlotEquiv
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))))

open Combinatorics in
/-- Consecutive interaction-slot standardization of an actual connected
component preserves the crossing count of its **restricted physical Wick
pairing**.  This is an exact crossing-number identity, not just a parity
congruence, and no assumption on the component interaction count is needed. -/
theorem ExternalInsertionDiagram.componentOrderedDiagram_pairing_crossingCount
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts) :
    (d.componentOrderedDiagram B).pairing.crossingCount =
      (d.restrictComponent B).pairing.crossingCount := by
  classical
  let T := interactionSector
    (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  have h : 2 * T.card + d.externalPairCount B =
      2 * (Finset.univ : Finset (Fin T.card)).card + d.externalPairCount B := by simp
  change PairingOn.crossingCount (r.pairing.transport
      (externalInsertionLegCongr (E := d.externalPairCount B)
        (standardSlotEquiv T)).symm) = r.pairing.crossingCount
  rw [externalInsertionLegCongr_standardize (E := d.externalPairCount B) T]
  have hcast := Pairing.cast_eq_transport h r.pairing
  rw [← hcast]
  exact Pairing.cast_crossingCount h r.pairing

/-- External times of one component in its canonical increasing external-slot order. -/
noncomputable def ExternalInsertionDiagram.componentExternalTime {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * d.externalPairCount B) → ℝ :=
  fun e => externalTime (d.externalSectorOrderIso B e).1

/-- Interaction times of one component in canonical increasing local interaction-slot order. -/
noncomputable def ExternalInsertionDiagram.componentInteractionTime {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n))) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card → ℝ :=
  fun v =>
    σ ((interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
        rfl v).1

/-- Embed a component-local canonical atomic leg into the ambient canonical atomic-leg order. -/
noncomputable def ExternalInsertionDiagram.componentOrderedLeg {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts) :
    OrderedExternalInsertionLeg (d.externalPairCount B)
        (interactionSector
          (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card →
      OrderedExternalInsertionLeg E n :=
  orderedExternalInsertionLegMap
    (fun e => (d.externalSectorOrderIso B e).1)
    (fun v =>
      ((interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
          rfl v).1)

/-- Embed a component-local mixed-time atomic position into the ambient mixed-time atomic order by
preserving the represented canonical leg. -/
noncomputable def ExternalInsertionDiagram.componentMixedPosition {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B)) →
      Fin (2 * (2 * n + E)) :=
  fun p =>
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
      (d.componentOrderedLeg B
        (externalInsertionMixedTimeOrderedAtomicLegEquiv
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B) p))

/-- The canonical embedding of one component's mixed positions preserves their mixed-time order. -/
theorem ExternalInsertionDiagram.componentMixedPosition_strictMono {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    StrictMono (d.componentMixedPosition externalTime σ B) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  exact externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
    (fExternal := fun e => (d.externalSectorOrderIso B e).1)
    (fInteraction := fun v : Fin T.card => (T.orderIsoOfFin rfl v).1)
    (fun _ _ hab => (d.externalSectorOrderIso B).strictMono hab)
    (fun _ _ hab => (T.orderIsoOfFin rfl).strictMono hab)
    externalTime σ

/-- Flattening a component-local canonical leg and then embedding it into the ambient diagram
agrees with embedding the canonical leg directly. -/
private theorem ExternalInsertionDiagram.componentOrderedLeg_fixedPosition {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts)
    (leg : OrderedExternalInsertionLeg (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card) :
    (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm
        (d.componentOrderedLeg B leg) =
      d.componentDiagramLeg B
        ((externalInsertionLegCongr (E := d.externalPairCount B)
          (Combinatorics.standardSlotEquiv
            (interactionSector
              (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))))).symm
          ((externalInsertionLegEquiv (d.externalPairCount B)
            (Finset.univ : Finset (Fin
              (interactionSector
                (B : Finset (ExternalInsertionVertex E
                  (Finset.univ : Finset (Fin n))))).card))).symm leg)) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  rw [← externalInsertionLegCongr_symm]
  cases leg with
  | inl e =>
      change _ = d.componentDiagramLeg B
        (externalInsertionLegCongr (Combinatorics.standardSlotEquiv T).symm
          (externalInsertionExternalLeg (d.externalPairCount B) _ e))
      rw [externalInsertionLegCongr_externalLeg, d.componentDiagramLeg_external B]
      rfl
  | inr vl =>
      rcases vl with ⟨v, l⟩
      change _ = d.componentDiagramLeg B
        (externalInsertionLegCongr (E := d.externalPairCount B)
          (Combinatorics.standardSlotEquiv T).symm
          (externalInsertionInteractionLeg v l))
      rw [externalInsertionLegCongr_interactionLeg, d.componentDiagramLeg_interaction B]
      rfl

/-- The diagram partner map on canonical legs commutes with the canonical component-leg embedding. -/
private theorem ExternalInsertionDiagram.atomicLegPartner_componentOrderedLeg {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts)
    (leg : OrderedExternalInsertionLeg (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card) :
    d.atomicLegPartner (d.componentOrderedLeg B leg) =
      d.componentOrderedLeg B ((d.componentOrderedDiagram B).atomicLegPartner leg) := by
  apply (externalInsertionLegEquiv E
    (Finset.univ : Finset (Fin n))).symm.injective
  rw [ExternalInsertionDiagram.atomicLegPartner, Equiv.symm_apply_apply]
  rw [d.componentOrderedLeg_fixedPosition B leg,
    d.componentOrderedLeg_fixedPosition B
      ((d.componentOrderedDiagram B).atomicLegPartner leg)]
  unfold ExternalInsertionDiagram.atomicLegPartner
  simp only [Equiv.symm_apply_apply]
  unfold ExternalInsertionDiagram.componentOrderedDiagram
  simp only [ExternalInsertionDiagram.slotCongr, Combinatorics.PairingOn.transport_partner,
    Equiv.symm_symm, Equiv.symm_apply_apply]
  exact (d.componentDiagramLeg_restrictComponent_pairing_partner B _).symm

/-- The ambient mixed-order pairing partner of an embedded component position is the embedding of
the component mixed-order pairing partner. -/
theorem ExternalInsertionDiagram.pairingInMixedOrder_partner_componentMixedPosition
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    (d.pairingInMixedOrder externalTime σ).partner
        (d.componentMixedPosition externalTime σ B p) =
      d.componentMixedPosition externalTime σ B
        (((d.componentOrderedDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).partner p) := by
  let localExternalTime := d.componentExternalTime externalTime B
  let localInteractionTime := d.componentInteractionTime σ B
  let localLeg :=
    externalInsertionMixedTimeOrderedAtomicLegEquiv
      localExternalTime localInteractionTime p
  have hLocal :
      (d.componentOrderedDiagram B).atomicLegPartner localLeg =
        externalInsertionMixedTimeOrderedAtomicLegEquiv
          localExternalTime localInteractionTime
          (((d.componentOrderedDiagram B).pairingInMixedOrder
            localExternalTime localInteractionTime).partner p) := by
    apply (externalInsertionMixedTimeOrderedAtomicLegEquiv
      localExternalTime localInteractionTime).symm.injective
    simpa only [externalInsertionMixedTimeOrderedAtomicLegPosition,
      localLeg, Equiv.symm_apply_apply] using
      ((d.componentOrderedDiagram B).pairingInMixedOrder_partner_legPosition
        localExternalTime localInteractionTime localLeg).symm
  unfold ExternalInsertionDiagram.componentMixedPosition
  rw [d.pairingInMixedOrder_partner_legPosition,
    d.atomicLegPartner_componentOrderedLeg B localLeg,
    hLocal]

/-- The dependent sum of all component-local mixed positions is equivalent to the ambient
mixed-position enumeration. This is obtained only by transporting the existing fixed component
shuffle through the local and ambient mixed/fixed position equivalences. -/
noncomputable def ExternalInsertionDiagram.componentMixedPositionEquiv
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (Σ B : d.vertexGraph.componentPartition.parts,
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
          d.externalPairCount B))) ≃
      Fin (2 * (2 * n + E)) :=
  (Equiv.sigmaCongrRight fun B : d.vertexGraph.componentPartition.parts =>
    let T := interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
    (externalInsertionMixedTimeOrderedAtomicLegEquiv
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)).trans
      ((externalInsertionLegEquiv (d.externalPairCount B)
        (Finset.univ : Finset (Fin T.card))).symm.trans
        (externalInsertionLegCongr (E := d.externalPairCount B)
          (Combinatorics.standardSlotEquiv T)).symm)).trans
    (d.componentLegShuffle.slotEquiv.trans
      (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm)

/-- The transported all-component position equivalence restricts on one component to the canonical
`componentMixedPosition` embedding. -/
@[simp]
theorem ExternalInsertionDiagram.componentMixedPositionEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    d.componentMixedPositionEquiv externalTime σ ⟨B, p⟩ =
      d.componentMixedPosition externalTime σ B p := by
  apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
  simp only [ExternalInsertionDiagram.componentMixedPositionEquiv,
    Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply,
    Equiv.apply_symm_apply]
  refine (d.componentOrderedLeg_fixedPosition B _).symm.trans ?_
  exact (externalInsertionMixedTimeAmbientPositionEquiv_legPosition
    externalTime σ _).symm

/-- The canonical family shuffle from component-local mixed atomic positions to the ambient
mixed-time atomic positions. -/
noncomputable def ExternalInsertionDiagram.componentMixedPositionShuffle
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Combinatorics.FamilySlotShuffleTo
      (fun B : d.vertexGraph.componentPartition.parts =>
        2 * (2 * (interactionSector
          (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
            d.externalPairCount B))
      (2 * (2 * n + E)) where
  slotEquiv := d.componentMixedPositionEquiv externalTime σ
  strictMono := fun B => by
    intro a b hab
    simpa only [Common.ExternalInsertionDiagram.componentMixedPositionEquiv_apply] using
      d.componentMixedPosition_strictMono externalTime σ B hab

@[simp]
theorem ExternalInsertionDiagram.componentMixedPositionShuffle_slotEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    (d.componentMixedPositionShuffle externalTime σ).slotEquiv ⟨B, p⟩ =
      d.componentMixedPosition externalTime σ B p :=
  d.componentMixedPositionEquiv_apply externalTime σ B p

end Common
end SecondQuantization
