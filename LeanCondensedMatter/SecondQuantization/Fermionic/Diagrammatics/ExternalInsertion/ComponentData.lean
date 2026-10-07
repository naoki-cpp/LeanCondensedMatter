import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.MixedOrderData
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentDecomposition

set_option linter.style.header false

/-!
# Component-local fermionic external-insertion data

A restricted external-insertion component retains its interaction vertices as a subset of the
ambient slots. The concrete fermionic amplitude layer instead uses consecutive `Fin m` interaction
slots. This module supplies the canonical increasing reindexing needed to apply the component diagram
data to one connected component, together with the induced local external and interaction times.
It identifies local canonical legs with their ambient counterparts and constructs the induced
mixed-position embeddings and normalized-pair equivalences. Timed-field and thermal-kernel
locality are proved in a separate Fermionic consumer module.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*}

/-- Reindex one connected component by consecutive interaction slots while preserving the canonical
component external order and restricted pairing. -/
noncomputable def ExternalInsertionWickDiagram.componentWickDiagram {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts) :
    ExternalInsertionWickDiagram Mode (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  exact {
    externalLabel := r.externalLabel
    vertexLabel := fun v => r.vertexLabel (T.orderIsoOfFin rfl v.1)
    pairing := Equiv.cast (by simp) r.pairing
  }

/-- External times of one component in its canonical increasing external-slot order. -/
noncomputable def ExternalInsertionWickDiagram.componentExternalTime {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * d.externalPairCount B) → ℝ :=
  fun e => externalTime (d.externalSectorOrderIso B e).1

/-- Interaction times of one component in canonical increasing local interaction-slot order. -/
noncomputable def ExternalInsertionWickDiagram.componentInteractionTime {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card → ℝ :=
  fun v =>
    σ ((interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
        rfl v).1

@[simp]
theorem ExternalInsertionWickDiagram.componentWickDiagram_externalLabel {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) :
    (d.componentWickDiagram B).externalLabel e =
      d.externalLabel (d.externalSectorOrderIso B e).1 := by
  rfl


/-- Embed a component-local canonical atomic leg into the ambient canonical atomic-leg order. -/
noncomputable def ExternalInsertionWickDiagram.componentOrderedLeg {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
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

/-- The canonical component-leg embedding is injective. -/
theorem ExternalInsertionWickDiagram.componentOrderedLeg_injective {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts) :
    Function.Injective (d.componentOrderedLeg B) :=
  orderedExternalInsertionLegMap_injective
    (Subtype.val_injective.comp (d.externalSectorOrderIso B).injective)
    (Subtype.val_injective.comp
      ((interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
          rfl).injective)

@[simp]
theorem ExternalInsertionWickDiagram.componentWickDiagram_vertexLabelSequence {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (v : Fin (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card) :
    (d.componentWickDiagram B).vertexLabelSequence v =
      d.vertexLabelSequence
        ((interactionSector
          (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
            rfl v).1 := by
  rfl

/-- Embed a component-local mixed-time atomic position into the ambient mixed-time atomic order by
preserving the represented canonical leg. -/
noncomputable def ExternalInsertionWickDiagram.componentMixedPosition {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
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
theorem ExternalInsertionWickDiagram.componentMixedPosition_strictMono {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
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
private theorem ExternalInsertionWickDiagram.componentOrderedLeg_fixedPosition {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (leg : OrderedExternalInsertionLeg (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card) :
    (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm
        (d.componentOrderedLeg B leg) =
      d.componentDiagramLeg B
        ((finCongr (by simp))
          ((externalInsertionLegEquiv (d.externalPairCount B)
            (Finset.univ : Finset (Fin
              (interactionSector
                (B : Finset (ExternalInsertionVertex E
                  (Finset.univ : Finset (Fin n))))).card))).symm leg)) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  cases leg with
  | inl e =>
      have hcast :
          (finCongr (by simp)
              ((externalInsertionLegEquiv (d.externalPairCount B)
                (Finset.univ : Finset (Fin T.card))).symm (Sum.inl e)) :
            Fin (2 * (2 * T.card + d.externalPairCount B))) =
            externalInsertionExternalLeg (d.externalPairCount B) T e := by
        apply Fin.ext
        change (externalInsertionExternalLeg (d.externalPairCount B)
          (Finset.univ : Finset (Fin T.card)) e).val =
            (externalInsertionExternalLeg (d.externalPairCount B) T e).val
        simp
      rw [hcast, d.componentDiagramLeg_external B]
      rfl
  | inr leg =>
      rcases leg with ⟨v, l⟩
      let vT : ↥T := T.orderIsoOfFin rfl v.1
      have hcast :
          (finCongr (by simp)
              ((externalInsertionLegEquiv (d.externalPairCount B)
                (Finset.univ : Finset (Fin T.card))).symm (Sum.inr (v, l))) :
            Fin (2 * (2 * T.card + d.externalPairCount B))) =
            externalInsertionInteractionLeg (E := d.externalPairCount B) vT l := by
        apply Fin.ext
        change (externalInsertionInteractionLeg (E := d.externalPairCount B)
          (v : ↥(Finset.univ : Finset (Fin T.card))) l).val =
            (externalInsertionInteractionLeg (E := d.externalPairCount B) vT l).val
        rw [externalInsertionInteractionLeg_val, externalInsertionInteractionLeg_val]
        have huniv :
            (((Finset.univ : Finset (Fin T.card)).orderIsoOfFin rfl).symm v).val =
              v.1.val := by
          rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
        have hT : ((T.orderIsoOfFin rfl).symm vT).val = v.1.val := by
          simp [vT]
        rw [huniv, hT]
      rw [hcast, d.componentDiagramLeg_interaction B]
      rfl

/-- The diagram partner map on canonical legs commutes with the canonical component-leg embedding. -/
private theorem ExternalInsertionWickDiagram.atomicLegPartner_componentOrderedLeg {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (leg : OrderedExternalInsertionLeg (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card) :
    d.atomicLegPartner (d.componentOrderedLeg B leg) =
      d.componentOrderedLeg B ((d.componentWickDiagram B).atomicLegPartner leg) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  let h : 2 * T.card + d.externalPairCount B =
      2 * (Finset.univ : Finset (Fin T.card)).card + d.externalPairCount B := by
    simp
  have hpair : (d.componentWickDiagram B).pairing =
      Equiv.cast (congrArg Combinatorics.Pairing h) r.pairing := by
    unfold ExternalInsertionWickDiagram.componentWickDiagram
    dsimp [T, r]
  have hfin : (finCongr (by simp) :
      Fin (2 * (2 * (Finset.univ : Finset (Fin T.card)).card +
        d.externalPairCount B)) ≃
      Fin (2 * (2 * T.card + d.externalPairCount B))) =
      finCongr (congrArg (fun k : ℕ => 2 * k) h.symm) := by
    congr
  apply (externalInsertionLegEquiv E
    (Finset.univ : Finset (Fin n))).symm.injective
  rw [ExternalInsertionWickDiagram.atomicLegPartner, Equiv.symm_apply_apply]
  rw [d.componentOrderedLeg_fixedPosition B leg,
    d.componentOrderedLeg_fixedPosition B
      ((d.componentWickDiagram B).atomicLegPartner leg)]
  unfold ExternalInsertionWickDiagram.atomicLegPartner
  simp only [Equiv.symm_apply_apply]
  rw [hpair, hfin, Combinatorics.Pairing.cast_partner h r.pairing]
  exact (d.componentDiagramLeg_restrictComponent_pairing_partner B _).symm

/-- The ambient mixed-order pairing partner of an embedded component position is the embedding of
the component mixed-order pairing partner. -/
theorem ExternalInsertionWickDiagram.pairingInMixedOrder_partner_componentMixedPosition
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    (d.pairingInMixedOrder externalTime σ).partner
        (d.componentMixedPosition externalTime σ B p) =
      d.componentMixedPosition externalTime σ B
        (((d.componentWickDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).partner p) := by
  let localExternalTime := d.componentExternalTime externalTime B
  let localInteractionTime := d.componentInteractionTime σ B
  let localLeg :=
    externalInsertionMixedTimeOrderedAtomicLegEquiv
      localExternalTime localInteractionTime p
  have hLocal :
      (d.componentWickDiagram B).atomicLegPartner localLeg =
        externalInsertionMixedTimeOrderedAtomicLegEquiv
          localExternalTime localInteractionTime
          (((d.componentWickDiagram B).pairingInMixedOrder
            localExternalTime localInteractionTime).partner p) := by
    have hPartner :=
      (d.componentWickDiagram B).pairingInMixedOrder_partner_legPosition
        localExternalTime localInteractionTime localLeg
    have h := congrArg
      (externalInsertionMixedTimeOrderedAtomicLegEquiv
        localExternalTime localInteractionTime) hPartner
    simpa [localLeg] using h.symm
  unfold ExternalInsertionWickDiagram.componentMixedPosition
  rw [d.pairingInMixedOrder_partner_legPosition,
    d.atomicLegPartner_componentOrderedLeg B localLeg,
    hLocal]

/-- Component-local transport from mixed-time atomic positions back to the canonical fixed
flattened positions. This is the local permutation used when comparing component shuffles with the
ambient mixed-time ordering permutation. -/
noncomputable def ExternalInsertionWickDiagram.componentMixedToFixedPositionEquiv
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
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
noncomputable def ExternalInsertionWickDiagram.componentMixedPositionEquiv
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
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
theorem ExternalInsertionWickDiagram.componentMixedPositionEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    d.componentMixedPositionEquiv externalTime σ ⟨B, p⟩ =
      d.componentMixedPosition externalTime σ B p := by
  apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
  simp only [ExternalInsertionWickDiagram.componentMixedPositionEquiv,
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
  have hlocal :
      d.componentMixedToFixedPositionEquiv externalTime σ B p =
        (finCongr (by simp))
          ((externalInsertionLegEquiv (d.externalPairCount B)
            (Finset.univ : Finset (Fin
              (interactionSector
                (B : Finset (ExternalInsertionVertex E
                  (Finset.univ : Finset (Fin n))))).card))).symm localLeg) := by
    unfold ExternalInsertionWickDiagram.componentMixedToFixedPositionEquiv
    apply Fin.ext
    change
      (externalInsertionMixedTimeAmbientPositionEquiv
        localExternalTime localInteractionTime p).val =
      ((externalInsertionLegEquiv (d.externalPairCount B)
        (Finset.univ : Finset (Fin
          (interactionSector
            (B : Finset (ExternalInsertionVertex E
              (Finset.univ : Finset (Fin n))))).card))).symm localLeg).val
    have hpos :
        externalInsertionMixedTimeAmbientPositionEquiv
            localExternalTime localInteractionTime p =
          (externalInsertionLegEquiv (d.externalPairCount B)
            (Finset.univ : Finset (Fin
              (interactionSector
                (B : Finset (ExternalInsertionVertex E
                  (Finset.univ : Finset (Fin n))))).card))).symm localLeg := by
      apply (externalInsertionLegEquiv (d.externalPairCount B)
        (Finset.univ : Finset (Fin
          (interactionSector
            (B : Finset (ExternalInsertionVertex E
              (Finset.univ : Finset (Fin n))))).card))).injective
      rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv]
      change localLeg =
        externalInsertionLegEquiv (d.externalPairCount B)
          (Finset.univ : Finset (Fin
            (interactionSector
              (B : Finset (ExternalInsertionVertex E
                (Finset.univ : Finset (Fin n))))).card))
          ((externalInsertionLegEquiv (d.externalPairCount B)
            (Finset.univ : Finset (Fin
              (interactionSector
                (B : Finset (ExternalInsertionVertex E
                  (Finset.univ : Finset (Fin n))))).card))).symm localLeg)
      exact (Equiv.apply_symm_apply _ localLeg).symm
    exact congrArg Fin.val hpos
  rw [hlocal, ← hfixed]
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
  unfold ExternalInsertionWickDiagram.componentMixedPosition
  exact hambient.symm

/-- Component-local mixed-order normalized pairs, over all connected components, are equivalent to
the ambient mixed-order normalized pairs. The position equivalence is only the fixed component
shuffle transported through mixed/fixed position equivalences. -/
noncomputable def ExternalInsertionWickDiagram.componentMixedPairEquiv
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (Σ B : d.vertexGraph.componentPartition.parts,
      ((d.componentWickDiagram B).pairingInMixedOrder
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B)).NormalizedPair) ≃
      (d.pairingInMixedOrder externalTime σ).NormalizedPair :=
  (d.pairingInMixedOrder externalTime σ).normalizedPairSigmaEquiv
    (fun B =>
      (d.componentWickDiagram B).pairingInMixedOrder
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B))
    (d.componentMixedPositionEquiv externalTime σ)
    (fun B p => by
      simpa only [ExternalInsertionWickDiagram.componentMixedPositionEquiv_apply] using
        d.pairingInMixedOrder_partner_componentMixedPosition externalTime σ B p)

/-- The all-component mixed pair equivalence maps a local normalized pair by applying
`componentMixedPosition` to its two endpoints. -/
@[simp]
theorem ExternalInsertionWickDiagram.componentMixedPairEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (pr : ((d.componentWickDiagram B).pairingInMixedOrder
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)).NormalizedPair) :
    (d.componentMixedPairEquiv externalTime σ ⟨B, pr⟩).1 =
      (d.componentMixedPosition externalTime σ B pr.1.1,
        d.componentMixedPosition externalTime σ B pr.1.2) := by
  let componentPairing := fun C : d.vertexGraph.componentPartition.parts =>
    (d.componentWickDiagram C).pairingInMixedOrder
      (d.componentExternalTime externalTime C)
      (d.componentInteractionTime σ C)
  let hpartner : ∀ C p,
      (d.pairingInMixedOrder externalTime σ).partner
          (d.componentMixedPositionEquiv externalTime σ ⟨C, p⟩) =
        d.componentMixedPositionEquiv externalTime σ
          ⟨C, (componentPairing C).partner p⟩ := by
    intro C p
    simpa only [ExternalInsertionWickDiagram.componentMixedPositionEquiv_apply] using
      d.pairingInMixedOrder_partner_componentMixedPosition externalTime σ C p
  simpa only [ExternalInsertionWickDiagram.componentMixedPairEquiv,
    ExternalInsertionWickDiagram.componentMixedPositionEquiv_apply] using
    (Combinatorics.Pairing.normalizedPairSigmaEquiv_apply_of_strictMono
      (d.pairingInMixedOrder externalTime σ)
      componentPairing
      (d.componentMixedPositionEquiv externalTime σ)
      hpartner
      (fun C => by
        simpa only [ExternalInsertionWickDiagram.componentMixedPositionEquiv_apply] using
          d.componentMixedPosition_strictMono externalTime σ C)
      B pr)


end Fermionic
end SecondQuantization
