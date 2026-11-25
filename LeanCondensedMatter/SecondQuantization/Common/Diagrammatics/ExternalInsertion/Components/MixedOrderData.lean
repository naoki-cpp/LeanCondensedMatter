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
      Finset.univ := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  exact {
    externalLabel := r.externalLabel
    vertexLabel := fun v => r.vertexLabel (T.orderIsoOfFin rfl v.1)
    pairing := Equiv.cast (by simp) r.pairing
  }

open Combinatorics in
/-- The consecutive interaction-slot component diagram is exactly the
canonical `slotCongr` relabeling of its actual connected-component
restriction. This retains its external labels, interaction labels and
flattened-leg Wick pairing. -/
theorem ExternalInsertionDiagram.componentOrderedDiagram_eq_slotCongr
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts) :
    let T := interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
    d.componentOrderedDiagram B =
      (d.restrictComponent B).slotCongr (standardSlotEquiv T) := by
  classical
  dsimp only
  let T := interactionSector
    (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  apply ExternalInsertionDiagram.ext
  · rfl
  · funext v
    change r.vertexLabel (T.orderIsoOfFin rfl v.1) =
      r.vertexLabel ((standardSlotEquiv T).symm v)
    congr 1
  · change (Equiv.cast (show Pairing (2 * T.card + d.externalPairCount B) =
          PairingOn (Fin (2 * (2 * (Finset.univ : Finset (Fin T.card)).card +
            d.externalPairCount B))) from by simp [Pairing]) r.pairing) =
        r.pairing.transport
          (externalInsertionLegCongr (E := d.externalPairCount B)
            (standardSlotEquiv T)).symm
    rw [externalInsertionLegCongr_standardize (E := d.externalPairCount B) T]
    exact Pairing.cast_eq_transport (by simp [T]) r.pairing


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
  change (Equiv.cast (show
      Pairing (2 * T.card + d.externalPairCount B) =
        Pairing (2 * (Finset.univ : Finset (Fin T.card)).card +
          d.externalPairCount B) from by simp)
      (d.restrictComponent B).pairing).crossingCount =
        (d.restrictComponent B).pairing.crossingCount
  exact Pairing.cast_crossingCount (by simp) _

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
  have hExternal : StrictMono (fun e : Fin (2 * d.externalPairCount B) =>
      (d.externalSectorOrderIso B e).1) := by
    intro a b hab
    exact (d.externalSectorOrderIso B).strictMono hab
  have hInteraction : StrictMono (fun v : Fin T.card =>
      (T.orderIsoOfFin rfl v).1) := by
    intro a b hab
    exact (T.orderIsoOfFin rfl).strictMono hab
  change StrictMono (fun p =>
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
      (orderedExternalInsertionLegMap
        (fun e => (d.externalSectorOrderIso B e).1)
        (fun v => (T.orderIsoOfFin rfl v).1)
        (externalInsertionMixedTimeOrderedAtomicLegEquiv
          (fun e => externalTime (d.externalSectorOrderIso B e).1)
          (fun v => σ (T.orderIsoOfFin rfl v).1) p)))
  exact
    externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
      hExternal hInteraction externalTime σ

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
      simp only [externalInsertionLegCongr, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
      change _ = d.componentDiagramLeg B
        (externalInsertionExternalLeg (d.externalPairCount B) T e)
      rw [d.componentDiagramLeg_external B]
      rfl
  | inr vl =>
      rcases vl with ⟨v, l⟩
      simp only [externalInsertionLegCongr, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.prodCongr_apply]
      change _ = d.componentDiagramLeg B
        (externalInsertionInteractionLeg (E := d.externalPairCount B)
          (T.orderIsoOfFin rfl v.1) l)
      rw [d.componentDiagramLeg_interaction B]
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
  rw [d.componentOrderedDiagram_eq_slotCongr B]
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
    have hPartner :=
      (d.componentOrderedDiagram B).pairingInMixedOrder_partner_legPosition
        localExternalTime localInteractionTime localLeg
    have hPosition :
        externalInsertionMixedTimeOrderedAtomicLegPosition
            localExternalTime localInteractionTime localLeg = p := by
      dsimp [localLeg, externalInsertionMixedTimeOrderedAtomicLegPosition]
      exact
        (externalInsertionMixedTimeOrderedAtomicLegEquiv
          localExternalTime localInteractionTime).symm_apply_apply p
    rw [hPosition] at hPartner
    have h := congrArg
      (externalInsertionMixedTimeOrderedAtomicLegEquiv
        localExternalTime localInteractionTime) hPartner.symm
    simpa [localLeg] using h
  unfold ExternalInsertionDiagram.componentMixedPosition
  rw [d.pairingInMixedOrder_partner_legPosition,
    d.atomicLegPartner_componentOrderedLeg B localLeg,
    hLocal]

private noncomputable def ExternalInsertionDiagram.componentMixedToFixedPositionEquiv
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B)) ≃
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
          d.externalPairCount B)) :=
  (externalInsertionMixedTimeAmbientPositionEquiv
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)).trans
    (finCongr (by simp))

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
  (Equiv.sigmaCongrRight fun B =>
      d.componentMixedToFixedPositionEquiv externalTime σ B).trans
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
  let localExternalTime := d.componentExternalTime externalTime B
  let localInteractionTime := d.componentInteractionTime σ B
  let localLeg :=
    externalInsertionMixedTimeOrderedAtomicLegEquiv
      localExternalTime localInteractionTime p
  have hfixed :=
    d.componentOrderedLeg_fixedPosition B localLeg
  let T := interactionSector
    (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let e := externalInsertionLegEquiv (d.externalPairCount B)
    (Finset.univ : Finset (Fin T.card))
  have hpos : externalInsertionMixedTimeAmbientPositionEquiv
      localExternalTime localInteractionTime p = e.symm localLeg := by
    apply e.injective
    calc
      e (externalInsertionMixedTimeAmbientPositionEquiv
          localExternalTime localInteractionTime p) = localLeg :=
        externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv
          localExternalTime localInteractionTime p
      _ = e (e.symm localLeg) := (e.apply_symm_apply localLeg).symm
  have hlocal :
      d.componentMixedToFixedPositionEquiv externalTime σ B p =
        (finCongr (by simp [T])) (e.symm localLeg) := by
    unfold ExternalInsertionDiagram.componentMixedToFixedPositionEquiv
    apply Fin.ext
    change (externalInsertionMixedTimeAmbientPositionEquiv
      localExternalTime localInteractionTime p).val = (e.symm localLeg).val
    exact congrArg Fin.val hpos
  rw [hlocal]
  rw [externalInsertionLegCongr_standardize] at hfixed
  refine hfixed.symm.trans ?_
  have hambient :
      externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
          (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
            (d.componentOrderedLeg B localLeg)) =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm
          (d.componentOrderedLeg B localLeg) := by
    apply (externalInsertionLegEquiv E
      (Finset.univ : Finset (Fin n))).injective
    rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
      externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
      Equiv.apply_symm_apply]
  unfold ExternalInsertionDiagram.componentMixedPosition
  exact hambient.symm

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
