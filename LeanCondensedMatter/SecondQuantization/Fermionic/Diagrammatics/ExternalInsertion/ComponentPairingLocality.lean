import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentData
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField

set_option linter.style.header false

/-!
# Component locality of fermionic external-insertion pair kernels

The canonical component-leg and mixed-position embeddings preserve timed fields and the concrete
free-Gibbs pair contraction. These physical statements depend on the Fermionic timed-field kernel;
the order and pairing correspondences themselves live in the kernel-free component-data layer.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- The timed field attached to a component-local canonical leg is exactly the ambient timed field
on the corresponding canonical leg. -/
omit [LinearOrder Mode] in
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
    [Fintype Mode] {E n : ℕ}
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
