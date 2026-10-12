import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentData
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField

set_option linter.style.header false

/-!
# Component locality of fermionic external-insertion pair kernels

The canonical component mixed-position embedding preserves the concrete free-Gibbs pair contraction
by specializing the general timed-field transport to the component external and interaction slots.
The order and pairing correspondences live in the kernel-free component-data layer.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

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
  let fExternal : Fin (2 * d.externalPairCount B) → Fin (2 * E) :=
    fun e => (d.externalSectorOrderIso B e).1
  let fInteraction := fun v =>
    ((interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
        rfl v).1
  simpa only [ExternalInsertionWickDiagram.componentMixedPosition,
    ExternalInsertionWickDiagram.componentOrderedLeg,
    ExternalInsertionWickDiagram.componentExternalTime,
    ExternalInsertionWickDiagram.componentInteractionTime,
    externalInsertionMixedTimeOrderedAtomicLegPosition, Equiv.symm_apply_apply,
    fExternal, fInteraction] using
    externalInsertionMixedTimeOrderedAtomicPairValue_map ε β fExternal fInteraction
      d.externalLabel externalTime d.vertexLabelSequence σ
      (externalInsertionMixedTimeOrderedAtomicLegEquiv
        (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B) a)
      (externalInsertionMixedTimeOrderedAtomicLegEquiv
        (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B) b)


end Fermionic
end SecondQuantization
