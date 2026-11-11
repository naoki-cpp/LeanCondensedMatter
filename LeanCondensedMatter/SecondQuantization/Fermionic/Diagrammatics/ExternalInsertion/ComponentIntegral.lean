import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.InteractionOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockAssembly
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentSlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Integral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceSign

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
    apply congrArg (fun localσ =>
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.componentOrderedDiagram B) ε β g
        (d.componentExternalTime externalTime B) localσ)
    funext j
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

/-- For a vacuum-free external-insertion diagram, reindex the *integrated*
Dyson component factorization by external-partition blocks rather than full
graph components. The interaction-order shuffle sum is essential:
individual ordered-simplex terms do not factor into component integrals.

This is the diagram-side reindexing needed for the signed source moment
identity; it uses the actual local Wick diagrams, local labels and times. -/
theorem ExternalInsertionWickDiagram.sum_componentInteractionOrderShuffle_orderedDysonAmplitude_eq_externalPartitionProduct
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      componentExternalOrderSign d blockOrder *
        ∏ P : (externalComponentPartition d.vertexGraph).parts,
          ExternalInsertionWickDiagram.dysonAmplitude
              (d.componentOrderedDiagram
                ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P))
              ε β g (d.componentExternalTime externalTime
                ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P)) := by
  classical
  let F : d.vertexGraph.componentPartition.parts → ℂ :=
    fun B => ExternalInsertionWickDiagram.dysonAmplitude
      (d.componentOrderedDiagram B) ε β g (d.componentExternalTime externalTime B)
  calc
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      componentExternalOrderSign d blockOrder * ∏ B, F B :=
        d.sum_componentInteractionOrderShuffle_orderedDysonAmplitude_eq_componentExternalOrderSign_mul_prod_components
          ε β g externalTime blockOrder
    _ = componentExternalOrderSign d blockOrder *
        ∏ P : (externalComponentPartition d.vertexGraph).parts,
          F ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P) := by
      congr 1
      exact (Equiv.prod_comp (d.vacuumFreeComponentsEquivExternalBlocks hVac).symm F).symm



/-- The summed interaction-order shuffle orbit of a vacuum-free physical
diagram factors with the **canonical fermionic external-partition source
sign**, not merely an arbitrarily ordered component sign. Each factor is
the integrated amplitude of its actual connected component with the
correct increasing local external labels and times. -/
theorem ExternalInsertionWickDiagram.sum_componentInteractionOrderShuffle_orderedDysonAmplitude_eq_sourceSign_mul_externalPartitionProduct
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      externalPartitionSourceSign (externalComponentPartition d.vertexGraph) *
        ∏ P : (externalComponentPartition d.vertexGraph).parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            (d.componentOrderedDiagram
              ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P))
            ε β g (d.componentExternalTime externalTime
              ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P)) := by
  rw [d.sum_componentInteractionOrderShuffle_orderedDysonAmplitude_eq_externalPartitionProduct
    hVac ε β g externalTime blockOrder]
  rw [externalPartitionSourceSign_eq_componentExternalOrderSign_of_vacuumFree
    d hVac blockOrder]

/-- For an *actually assembled* family of connected external blocks,
the interaction-time shuffle orbit of the physical Wick diagram carries
the prescribed external-source partition sign and factors into its
standalone connected-component Dyson amplitudes.

The components on the right are still indexed through the physical
assembled graph. Identifying each one with the independently supplied
local diagram, including its canonical slot relabelling, is the
remaining diagram-to-coefficient bridge. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit
    {E n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      externalPartitionSourceSign layout.partition *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude (d.componentOrderedDiagram B) ε β g
            (d.componentExternalTime externalTime B) := by
  classical
  let d : ExternalInsertionWickDiagram Mode E n :=
    layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  let blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts) :=
    Fintype.equivFin d.vertexGraph.componentPartition.parts
  have hVac : HasNoVacuumComponent d.vertexGraph :=
    layout.hasNoVacuumComponent_assembleDiagram
      (Finset.univ : Finset (Fin n)) F hconnected
  have hpart : externalComponentPartition d.vertexGraph = layout.partition :=
    layout.externalComponentPartition_assembleDiagram
      (Finset.univ : Finset (Fin n)) F hconnected
  have hsign :=
    externalPartitionSourceSign_eq_componentExternalOrderSign_of_vacuumFree
      d hVac blockOrder
  have horbit :=
    d.sum_componentInteractionOrderShuffle_orderedDysonAmplitude_eq_componentExternalOrderSign_mul_prod_components
      ε β g externalTime blockOrder
  calc
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude (d.componentOrderedDiagram B) ε β g
            (d.componentExternalTime externalTime B) := horbit
    _ = externalPartitionSourceSign layout.partition *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude (d.componentOrderedDiagram B) ε β g
            (d.componentExternalTime externalTime B) := by
      rw [← hsign, hpart]


/-- The physical signed shuffle orbit of independently assembled connected
Wick blocks, now written entirely in terms of the *canonical slot
transport of the actual restricted components*. This removes the
otherwise implicit consecutive-slot relabeling from each local factor.

The subsequent identification of those restrictions with the original
independent block-family data `F` remains a separate graph-component
and pairing-fiber compatibility theorem. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_slotCongr
    {E n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      externalPartitionSourceSign layout.partition *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            ((d.restrictComponent B).slotCongr (Combinatorics.standardSlotEquiv
              (interactionSector
                (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))))))
            ε β g (d.componentExternalTime externalTime B) := by
  classical
  let d : ExternalInsertionWickDiagram Mode E n :=
    layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  calc
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      externalPartitionSourceSign layout.partition *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            (d.componentOrderedDiagram B) ε β g
            (d.componentExternalTime externalTime B) :=
      ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit
        layout F hconnected ε β g externalTime
    _ = _ := by
      apply congrArg
        (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
      apply Finset.prod_congr rfl
      intro B _
      exact congrArg
        (fun localDiagram =>
          ExternalInsertionWickDiagram.dysonAmplitude localDiagram ε β g
            (d.componentExternalTime externalTime B))
        (d.componentOrderedDiagram_eq_slotCongr B)


end Fermionic
end SecondQuantization
