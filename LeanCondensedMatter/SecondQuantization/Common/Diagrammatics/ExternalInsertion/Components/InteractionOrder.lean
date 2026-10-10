import LeanCondensedMatter.Combinatorics.FamilyOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered

set_option linter.style.header false

/-!
# Component-local interaction orders for external-insertion diagrams

Interaction-time integrations order only the quartic interaction vertices, while connected
components are formed from both external and interaction vertices. Consequently some component
fibers may contain no interaction vertices. This module assembles component-local interaction
orders using the generic finite-family machinery without dropping zero-size component blocks.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- One interaction-vertex order for every connected component. Components with no interaction
vertices contribute the unique order on an empty fiber. -/
abbrev ExternalInsertionDiagram.ComponentInteractionOrders
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :=
  FamilyOrdersOf
    (fun B : d.vertexGraph.componentPartition.parts =>
      ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S))))
    (fun B : d.vertexGraph.componentPartition.parts =>
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card)

/-- Canonical increasing interaction-vertex order on every connected component. -/
noncomputable def ExternalInsertionDiagram.canonicalComponentInteractionOrders
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.ComponentInteractionOrders :=
  fun B =>
    ((interactionSector
      (B : Finset (ExternalInsertionVertex E S))).orderIsoOfFin rfl).toEquiv

/-- An order-preserving interleaving of component-local interaction slots into the ambient
interaction-time slots. Zero-size component blocks are retained. -/
abbrev ExternalInsertionDiagram.ComponentInteractionOrderShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :=
  FamilySlotShuffleTo
    (fun B : d.vertexGraph.componentPartition.parts =>
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card)
    S.card

/-- Assemble an ambient interaction-vertex order from component-local interaction orders and an
order-preserving component shuffle. -/
noncomputable def ExternalInsertionDiagram.assembleInteractionOrder
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (orders : d.ComponentInteractionOrders)
    (shuffle : d.ComponentInteractionOrderShuffle) :
    QuarticVertexOrder S :=
  assembleFamilyOrderOfSize
    (fun B : d.vertexGraph.componentPartition.parts =>
      ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S))))
    (fun B : d.vertexGraph.componentPartition.parts =>
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card)
    (interactionSectorComponentEquiv d.vertexGraph) orders shuffle

/-- Under an assembled interaction order, the ambient slot of a component-local vertex is exactly
the slot selected by the component shuffle. -/
@[simp]
theorem ExternalInsertionDiagram.assembleInteractionOrder_symm_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (orders : d.ComponentInteractionOrders)
    (shuffle : d.ComponentInteractionOrderShuffle)
    (B : d.vertexGraph.componentPartition.parts)
    (j : Fin (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card) :
    (d.assembleInteractionOrder orders shuffle).symm
        ⟨(orders B j).1,
          interactionSector_subset
            (B : Finset (ExternalInsertionVertex E S)) (orders B j).2⟩ =
      shuffle.slotEquiv ⟨B, j⟩ := by
  have h :=
    assembleFamilyOrderOfSize_symm_apply
      (fun B : d.vertexGraph.componentPartition.parts =>
        ↥(interactionSector
          (B : Finset (ExternalInsertionVertex E S))))
      (fun B : d.vertexGraph.componentPartition.parts =>
        (interactionSector
          (B : Finset (ExternalInsertionVertex E S))).card)
      (interactionSectorComponentEquiv d.vertexGraph) orders shuffle B j
  have hambient :
      (⟨(orders B j).1,
          interactionSector_subset
            (B : Finset (ExternalInsertionVertex E S)) (orders B j).2⟩ : ↥S) =
        (interactionSectorComponentEquiv d.vertexGraph).symm ⟨B, orders B j⟩ := by
    apply Subtype.ext
    exact (interactionSectorComponentEquiv_symm_val
      d.vertexGraph ⟨B, orders B j⟩).symm
  rw [hambient]
  simpa [ExternalInsertionDiagram.assembleInteractionOrder] using h

end Common
end SecondQuantization
