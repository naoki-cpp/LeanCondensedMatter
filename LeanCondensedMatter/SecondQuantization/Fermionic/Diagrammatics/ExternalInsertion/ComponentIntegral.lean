import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.InteractionOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Integral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity

set_option linter.style.header false

/-!
# Ordered-simplex component factorization for external insertions

The fixed-time Dyson amplitude already provides standalone connected-component integrands. This
module consumes their basic ordered-simplex amplitudes and applies the finite-family shuffle theorem to the
component-local integrands. The product of standalone component integrals is recovered after summing
over all order-preserving interleavings of the component-local interaction slots.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
/-- Pulling an assembled global interaction order back to one component gives exactly that
component's shuffle coordinates when the local component orders are canonical. -/
private theorem ExternalInsertionWickDiagram.componentInteractionTime_assembleInteractionOrder
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (shuffle : d.ComponentInteractionOrderShuffle)
    (τ : Fin (Finset.univ : Finset (Fin n)).card → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    d.componentInteractionTime
        (fun v =>
          τ ((d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle).symm
            ⟨v, Finset.mem_univ v⟩))
        B =
      shuffle.timeAssignment τ B := by
  funext j
  unfold Common.ExternalInsertionDiagram.componentInteractionTime
    FamilySlotShuffleTo.timeAssignment
  change
    τ ((d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle).symm
      ⟨((interactionSector
        (B : Finset (ExternalInsertionVertex E
          (Finset.univ : Finset (Fin n))))).orderIsoOfFin rfl j).1,
        Finset.mem_univ _⟩) =
      τ (shuffle.slotEquiv ⟨B, j⟩)
  apply congrArg τ
  have hslot :=
    d.assembleInteractionOrder_symm_apply
      d.canonicalComponentInteractionOrders shuffle B j
  rw [← hslot]
  apply congrArg
    (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle).symm
  apply Subtype.ext
  rfl

/-- The interaction-order shuffle orbit of an arbitrary external-insertion diagram factors into
the fixed external regrouping sign times the product of the standalone component amplitudes. -/
theorem ExternalInsertionWickDiagram.sum_componentInteractionOrderShuffle_orderedDysonAmplitude_eq_componentExternalOrderSign_mul_prod_components
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude (d.componentOrderedDiagram B) ε β g
            (d.componentExternalTime externalTime B) := by
  classical
  let size : d.vertexGraph.componentPartition.parts → ℕ :=
    fun B =>
      (interactionSector
        (B : Finset (ExternalInsertionVertex E
          (Finset.univ : Finset (Fin n))))).card
  let localIntegrand : ∀ B : d.vertexGraph.componentPartition.parts,
      (Fin (size B) → ℝ) → ℂ :=
    fun B localσ =>
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.componentOrderedDiagram B) ε β g
        (d.componentExternalTime externalTime B) localσ
  have hfactor (shuffle : d.ComponentInteractionOrderShuffle) :
      (fun τ =>
        d.dysonFixedTimeAmplitude ε β g externalTime
          (fun v =>
            τ ((d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle).symm
              ⟨v, Finset.mem_univ v⟩))) =
        (fun τ =>
          componentExternalOrderSign d blockOrder *
            shuffle.ambientIntegrand localIntegrand τ) := by
    funext τ
    rw [d.dysonFixedTimeAmplitude_eq_componentExternalOrderSign_mul_prod_components
      ε β g externalTime _ blockOrder]
    apply congrArg (fun z : ℂ => componentExternalOrderSign d blockOrder * z)
    unfold FamilySlotShuffleTo.ambientIntegrand
    apply Finset.prod_congr rfl
    intro B _
    change
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.componentOrderedDiagram B) ε β g
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime
            (fun v =>
              τ ((d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle).symm
                ⟨v, Finset.mem_univ v⟩))
            B) =
        ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.componentOrderedDiagram B) ε β g
          (d.componentExternalTime externalTime B)
          (shuffle.timeAssignment τ B)
    rw [d.componentInteractionTime_assembleInteractionOrder shuffle τ B]
  have hlocal (B : d.vertexGraph.componentPartition.parts) :
      intervalIntegral.MeasurableLocallyBounded (localIntegrand B) := by
    simpa [size, localIntegrand] using
      ExternalInsertionWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude (d.componentOrderedDiagram B)
        ε β g (d.componentExternalTime externalTime B)
  have hTotal : (∑ B, size B) = (Finset.univ : Finset (Fin n)).card := by
    simpa [size] using
      (sum_interactionSector_card_eq d.vertexGraph)
  have hshuffle :=
    FamilySlotShuffleTo.sum_integral_eq_prod
      size (Finset.univ : Finset (Fin n)).card hTotal β localIntegrand
      (fun B => by simpa [size, localIntegrand] using hlocal B)
  change
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      intervalIntegral.orderedSimplexIntegral
        (Finset.univ : Finset (Fin n)).card β
        (fun τ =>
          d.dysonFixedTimeAmplitude ε β g externalTime
            (fun v =>
              τ ((d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle).symm
                ⟨v, Finset.mem_univ v⟩)))) =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude (d.componentOrderedDiagram B) ε β g
            (d.componentExternalTime externalTime B)
  rw [Finset.sum_congr rfl fun shuffle _ => by
    rw [hfactor shuffle, intervalIntegral.orderedSimplexIntegral_smul]]
  rw [← Finset.mul_sum, hshuffle]
  apply congrArg (fun z : ℂ => componentExternalOrderSign d blockOrder * z)
  apply Finset.prod_congr rfl
  intro B _
  exact ExternalInsertionWickDiagram.orderedSimplexIntegral_dysonFixedTimeAmplitude
      (d.componentOrderedDiagram B)
    ε β g (d.componentExternalTime externalTime B)

end Fermionic
end SecondQuantization
