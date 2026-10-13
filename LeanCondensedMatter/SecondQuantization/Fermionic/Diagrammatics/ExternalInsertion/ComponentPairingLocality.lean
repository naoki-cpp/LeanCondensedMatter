import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
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
        (d.componentOrderedDiagram B).externalLabel
        (d.componentExternalTime externalTime B)
        (d.componentOrderedDiagram B).vertexLabelSequence
        (d.componentInteractionTime σ B) a b := by
  let fExternal : Fin (2 * d.externalPairCount B) → Fin (2 * E) :=
    fun e => (d.externalSectorOrderIso B e).1
  let fInteraction := fun v =>
    ((interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
        rfl v).1
  have hExternalLabel :
      d.externalLabel ∘ fExternal = (d.componentOrderedDiagram B).externalLabel := rfl
  have hExternalTime :
      externalTime ∘ fExternal = d.componentExternalTime externalTime B := rfl
  have hVertexLabel :
      d.vertexLabelSequence ∘ fInteraction =
        (d.componentOrderedDiagram B).vertexLabelSequence := rfl
  have hInteractionTime :
      σ ∘ fInteraction = d.componentInteractionTime σ B := rfl
  have h :=
    externalInsertionMixedTimeOrderedAtomicPairValue_map ε β fExternal fInteraction
      d.externalLabel externalTime d.vertexLabelSequence σ
      (externalInsertionMixedTimeOrderedAtomicLegEquiv
        (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B) a)
      (externalInsertionMixedTimeOrderedAtomicLegEquiv
        (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B) b)
  rw [hExternalLabel, hExternalTime, hVertexLabel, hInteractionTime] at h
  have hposition (p) :
      externalInsertionMixedTimeOrderedAtomicLegPosition
          (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B)
          (externalInsertionMixedTimeOrderedAtomicLegEquiv
            (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B) p) = p :=
    (externalInsertionMixedTimeOrderedAtomicLegEquiv
      (d.componentExternalTime externalTime B) (d.componentInteractionTime σ B)).symm_apply_apply p
  rw [hposition a, hposition b] at h
  exact h


end Fermionic
end SecondQuantization
