import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField

set_option linter.style.header false

/-!
# Component-local fermionic external-insertion data

A restricted external-insertion component retains its interaction vertices as a subset of the
ambient slots. The concrete fermionic amplitude layer instead uses consecutive `Fin m` interaction
slots. This module supplies the canonical increasing reindexing needed to apply that amplitude to
one connected component, together with the induced local external and interaction times. It also
identifies each local canonical atomic leg with its ambient canonical leg and proves that the
attached timed field is preserved by this embedding. The same semantic embedding is then lifted to
mixed-time positions, where the free-Gibbs pair kernel agrees with the standalone component kernel.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
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

/-- The timed field attached to a component-local canonical leg is exactly the ambient timed field
on the corresponding canonical leg. -/
theorem ExternalInsertionWickDiagram.orderedExternalInsertionLegField_componentOrderedLeg
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (leg : OrderedExternalInsertionLeg (d.externalPairCount B)
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card) :
    orderedExternalInsertionLegField
        (d.componentWickDiagram B).externalLabel
        (d.componentExternalTime externalTime B)
        (d.componentWickDiagram B).vertexLabelSequence
        (d.componentInteractionTime σ B) leg =
      orderedExternalInsertionLegField d.externalLabel externalTime
        d.vertexLabelSequence σ (d.componentOrderedLeg B leg) := by
  cases leg with
  | inl e =>
      rfl
  | inr leg =>
      rcases leg with ⟨v, l⟩
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

/-- Embed a component Wick diagram's fixed flattened position into the ambient diagram's fixed
flattened position. The small cast only identifies the component's consecutive interaction slots
with the equally-sized restricted interaction sector. -/
private noncomputable def ExternalInsertionWickDiagram.componentFixedPosition {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * (2 * (Finset.univ : Finset (Fin
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card)).card +
      d.externalPairCount B)) →
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + E)) :=
  fun p => d.componentDiagramLeg B ((finCongr (by simp)) p)

/-- Reading an embedded component fixed position as a canonical leg agrees with the direct
component canonical-leg embedding. -/
private theorem ExternalInsertionWickDiagram.externalInsertionLegEquiv_componentFixedPosition
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (Finset.univ : Finset (Fin
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card)).card +
      d.externalPairCount B))) :
    externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
        (d.componentFixedPosition B p) =
      d.componentOrderedLeg B
        (externalInsertionLegEquiv (d.externalPairCount B)
          (Finset.univ : Finset (Fin
            (interactionSector
              (B : Finset (ExternalInsertionVertex E
                (Finset.univ : Finset (Fin n))))).card)) p) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let localEquiv :=
    externalInsertionLegEquiv (d.externalPairCount B)
      (Finset.univ : Finset (Fin T.card))
  generalize hleg : localEquiv p = leg
  have hp : p = localEquiv.symm leg := by
    rw [← hleg]
    exact (localEquiv.symm_apply_apply p).symm
  rw [hp]
  rcases leg with e | ⟨v, l⟩
  · have hcast :
        (finCongr (by simp) (localEquiv.symm (Sum.inl e)) :
          Fin (2 * (2 * T.card + d.externalPairCount B))) =
          externalInsertionExternalLeg (d.externalPairCount B) T e := by
        apply Fin.ext
        change (externalInsertionExternalLeg (d.externalPairCount B)
          (Finset.univ : Finset (Fin T.card)) e).val = e.val
        simp
    rw [ExternalInsertionWickDiagram.componentFixedPosition, hcast,
      d.componentDiagramLeg_external B]
    simp [ExternalInsertionWickDiagram.componentOrderedLeg, externalInsertionExternalLeg]
  · let vT : ↥T := T.orderIsoOfFin rfl v.1
    have hcast :
        (finCongr (by simp) (localEquiv.symm (Sum.inr (v, l))) :
          Fin (2 * (2 * T.card + d.externalPairCount B))) =
          externalInsertionInteractionLeg (E := d.externalPairCount B) vT l := by
      apply Fin.ext
      change (externalInsertionInteractionLeg (E := d.externalPairCount B)
        (v : ↥(Finset.univ : Finset (Fin T.card))) l).val =
          2 * d.externalPairCount B + l.val + 4 * v.val
      simp [externalInsertionInteractionLeg_val]
    rw [ExternalInsertionWickDiagram.componentFixedPosition, hcast,
      d.componentDiagramLeg_interaction B]
    simp [ExternalInsertionWickDiagram.componentOrderedLeg, vT,
      externalInsertionInteractionLeg]

/-- The fixed-position embedding intertwines the component Wick pairing with the ambient pairing. -/
private theorem ExternalInsertionWickDiagram.componentFixedPosition_partner {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (Finset.univ : Finset (Fin
      (interactionSector
        (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card)).card +
      d.externalPairCount B))) :
    d.componentFixedPosition B ((d.componentWickDiagram B).pairing.partner p) =
      d.pairing.partner (d.componentFixedPosition B p) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  let h : 2 * T.card + d.externalPairCount B =
      2 * (Finset.univ : Finset (Fin T.card)).card + d.externalPairCount B := by
    simp
  have hpair : (d.componentWickDiagram B).pairing =
      Equiv.cast (congrArg Pairing h) r.pairing := by
    unfold ExternalInsertionWickDiagram.componentWickDiagram
    dsimp [T, r]
  have hfin : (finCongr (by simp) :
      Fin (2 * (2 * (Finset.univ : Finset (Fin T.card)).card +
        d.externalPairCount B)) ≃
      Fin (2 * (2 * T.card + d.externalPairCount B))) =
      finCongr (congrArg (fun k : ℕ => 2 * k) h.symm) := by
    congr
  unfold ExternalInsertionWickDiagram.componentFixedPosition
  rw [hpair, hfin, Pairing.cast_partner h r.pairing p]
  exact d.componentDiagramLeg_restrictComponent_pairing_partner B
    ((finCongr (congrArg (fun k : ℕ => 2 * k) h.symm)) p)

/-- The ambient fixed position underlying an embedded component mixed position is the fixed-position
embedding of the component's own underlying mixed position. -/
private theorem ExternalInsertionWickDiagram.mixedTimeAmbientPositionEquiv_componentMixedPosition
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
        (d.componentMixedPosition externalTime σ B p) =
      d.componentFixedPosition B
        (externalInsertionMixedTimeAmbientPositionEquiv
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B) p) := by
  apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).injective
  rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    d.externalInsertionLegEquiv_componentFixedPosition B,
    ExternalInsertionWickDiagram.componentMixedPosition,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv]

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
  apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
  rw [d.mixedTimeAmbientPositionEquiv_partner,
    d.mixedTimeAmbientPositionEquiv_componentMixedPosition externalTime σ B,
    d.mixedTimeAmbientPositionEquiv_componentMixedPosition externalTime σ B,
    (d.componentWickDiagram B).mixedTimeAmbientPositionEquiv_partner,
    d.componentFixedPosition_partner B]

private theorem
    ExternalInsertionWickDiagram.mixedTimeOrderedAtomicFieldFamily_componentMixedPosition
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    externalInsertionMixedTimeOrderedAtomicFieldFamily
        d.externalLabel externalTime d.vertexLabelSequence σ
        (d.componentMixedPosition externalTime σ B p) =
      externalInsertionMixedTimeOrderedAtomicFieldFamily
        (d.componentWickDiagram B).externalLabel
        (d.componentExternalTime externalTime B)
        (d.componentWickDiagram B).vertexLabelSequence
        (d.componentInteractionTime σ B) p := by
  unfold externalInsertionMixedTimeOrderedAtomicFieldFamily
  simp only [ExternalInsertionWickDiagram.componentMixedPosition,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position]
  rw [← d.orderedExternalInsertionLegField_componentOrderedLeg externalTime σ B]

/-- The ambient free-Gibbs pair contraction restricts to the standalone component pair contraction
under the canonical mixed-position embedding. -/
theorem ExternalInsertionWickDiagram.externalInsertionMixedTimeOrderedAtomicPairValue_componentMixedPosition
    [LinearOrder Mode] [Fintype Mode] {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (a b : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
        d.externalLabel externalTime d.vertexLabelSequence σ
        (d.componentMixedPosition externalTime σ B a)
        (d.componentMixedPosition externalTime σ B b) =
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
        (d.componentWickDiagram B).externalLabel
        (d.componentExternalTime externalTime B)
        (d.componentWickDiagram B).vertexLabelSequence
        (d.componentInteractionTime σ B) a b := by
  unfold externalInsertionMixedTimeOrderedAtomicPairValue
  rw [d.mixedTimeOrderedAtomicFieldFamily_componentMixedPosition externalTime σ B a,
    d.mixedTimeOrderedAtomicFieldFamily_componentMixedPosition externalTime σ B b]

end Fermionic
end SecondQuantization
