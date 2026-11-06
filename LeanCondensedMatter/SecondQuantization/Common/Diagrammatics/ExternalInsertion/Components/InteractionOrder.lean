import LeanCondensedMatter.Combinatorics.Shuffle.FamilyOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
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

/-- A vacuum-free diagram's total interaction order is the sum of the local
interaction orders indexed by *external partition blocks*.

This is the cardinality identity that makes external-block shuffle
decomposition possible, including blocks carrying zero interaction vertices. -/
theorem ExternalInsertionDiagram.sum_externalBlockInteractionSector_card_eq
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph) :
    (∑ P : (externalComponentPartition d.vertexGraph).parts,
      (interactionSector
        (((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P).1 :
          Finset (ExternalInsertionVertex E S))).card) = S.card := by
  classical
  let e := d.vacuumFreeComponentsEquivExternalBlocks hVac
  let size : d.vertexGraph.componentPartition.parts → ℕ :=
    fun B => (interactionSector (B.1 : Finset (ExternalInsertionVertex E S))).card
  calc
    (∑ P : (externalComponentPartition d.vertexGraph).parts,
      (interactionSector
        (((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P).1 :
          Finset (ExternalInsertionVertex E S))).card) =
      ∑ B : d.vertexGraph.componentPartition.parts, size B := by
        exact Equiv.sum_comp e.symm size
    _ = S.card := by
      simpa [size] using sum_interactionSector_card_eq d.vertexGraph

/-- The actual interaction-order shuffle family of a vacuum-free diagram,
initially indexed by full graph components, is equivalent to a family
indexed by the external insertion partition.

This transports the *whole finite shuffle index type*, not just its
cardinality or an arbitrary representative. In particular, zero-interaction
external blocks remain present in the family. -/
noncomputable def ExternalInsertionDiagram.vacuumFreeExternalBlockInteractionShuffleEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph) :
    d.ComponentInteractionOrderShuffle ≃
      FamilySlotShuffleTo
        (fun P : (externalComponentPartition d.vertexGraph).parts =>
          (interactionSector
            (((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P).1 :
              Finset (ExternalInsertionVertex E S))).card)
        S.card := by
  classical
  let e := d.vacuumFreeComponentsEquivExternalBlocks hVac
  let size : d.vertexGraph.componentPartition.parts → ℕ :=
    fun B => (interactionSector (B.1 : Finset (ExternalInsertionVertex E S))).card
  have hs : (∑ B, size B) = S.card := by
    simpa [size] using sum_interactionSector_card_eq d.vertexGraph
  have hsP : (∑ P, size (e.symm P)) = S.card := by
    calc
      (∑ P, size (e.symm P)) = ∑ B, size B := Equiv.sum_comp e.symm size
      _ = S.card := hs
  exact
    ((FamilySlotShuffleTo.castTotalEquiv hs.symm).trans
      (FamilySlotShuffle.reindexEquiv e.symm size)).trans
      (FamilySlotShuffleTo.castTotalEquiv hsP)


end Common
end SecondQuantization
