import LeanCondensedMatter.Combinatorics.FamilyOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered

set_option linter.style.header false

/-!
# Component-local interaction orders for external-insertion diagrams

Interaction-time integrations order only the quartic interaction vertices, while connected
components are formed from both external and interaction vertices. Consequently some component
fibers may contain no interaction vertices. This module applies the generic finite-family order
decomposition to those interaction fibers without dropping zero-size component blocks.
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
  FamilyOrders fun B : d.vertexGraph.componentPartition.parts =>
    ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))

/-- An order-preserving interleaving of component-local interaction slots into the ambient
interaction-time slots. Zero-size component blocks are retained. -/
abbrev ExternalInsertionDiagram.ComponentInteractionOrderShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :=
  FamilySlotShuffleTo
    (fun B : d.vertexGraph.componentPartition.parts =>
      Fintype.card ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S))))
    S.card

/-- The ambient interaction vertices are the disjoint union of their component interaction
sectors. -/
noncomputable def ExternalInsertionDiagram.interactionVertexComponentEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    ↥S ≃
      Σ B : d.vertexGraph.componentPartition.parts,
        ↥(interactionSector
          (B : Finset (ExternalInsertionVertex E S))) :=
  d.vertexGraph.componentPartition.equivSigmaSubfinsets
    S
    (fun v : ↥S => (Sum.inr v : ExternalInsertionVertex E S))
    (fun _ => Finset.mem_univ _)
    (fun B => interactionSector
      (B : Finset (ExternalInsertionVertex E S)))
    (fun B => interactionSector_subset
      (B : Finset (ExternalInsertionVertex E S)))
    (fun B v => mem_interactionSector_subtype
      (B : Finset (ExternalInsertionVertex E S)) v)

@[simp]
theorem ExternalInsertionDiagram.interactionVertexComponentEquiv_symm_val
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (x : Σ B : d.vertexGraph.componentPartition.parts,
      ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S)))) :
    ((d.interactionVertexComponentEquiv.symm x : ↥S) : Fin N) = (x.2 : Fin N) :=
  rfl

/-- Assemble an ambient interaction-vertex order from component-local interaction orders and an
order-preserving component shuffle. -/
noncomputable def ExternalInsertionDiagram.assembleInteractionOrder
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (orders : d.ComponentInteractionOrders)
    (shuffle : d.ComponentInteractionOrderShuffle) :
    QuarticVertexOrder S :=
  assembleFamilyOrder
    (fun B : d.vertexGraph.componentPartition.parts =>
      ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S))))
    d.interactionVertexComponentEquiv orders shuffle

/-- A global interaction-vertex order is equivalent to component-local interaction orders together
with an order-preserving component shuffle. Empty interaction sectors remain represented as
zero-size shuffle blocks. -/
noncomputable def ExternalInsertionDiagram.componentInteractionOrderDecompositionEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    QuarticVertexOrder S ≃
      d.ComponentInteractionOrders × d.ComponentInteractionOrderShuffle :=
  familyOrderDecompositionEquiv
    (fun B : d.vertexGraph.componentPartition.parts =>
      ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S))))
    d.interactionVertexComponentEquiv

end Common
end SecondQuantization
