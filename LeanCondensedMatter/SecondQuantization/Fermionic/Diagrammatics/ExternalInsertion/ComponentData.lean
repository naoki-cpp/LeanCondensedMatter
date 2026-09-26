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
attached timed field is preserved by this embedding.
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
      OrderedExternalInsertionLeg E n
  | .inl e => .inl (d.externalSectorOrderIso B e).1
  | .inr leg =>
      .inr
        (⟨((interactionSector
          (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
            rfl leg.1.1).1, Finset.mem_univ _⟩, leg.2)

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

end Fermionic
end SecondQuantization
