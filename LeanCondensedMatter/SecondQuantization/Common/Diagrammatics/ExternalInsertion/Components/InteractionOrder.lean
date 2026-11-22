import LeanCondensedMatter.Combinatorics.Shuffle.FamilyOrderShuffle
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

/-- The canonical interleaving of the actual component interaction
fibers is the shuffle extracted from the canonical increasing ambient
vertex order. It retains components without interaction vertices. -/
noncomputable def ExternalInsertionDiagram.canonicalComponentInteractionShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.ComponentInteractionOrderShuffle := by
  classical
  exact ((familyOrderDecompositionEquivOfSize
    (fun B : d.vertexGraph.componentPartition.parts =>
      ↥(interactionSector (B : Finset (ExternalInsertionVertex E S))))
    (fun B : d.vertexGraph.componentPartition.parts =>
      (interactionSector (B : Finset (ExternalInsertionVertex E S))).card)
    (fun _ => by simp)
    (interactionSectorComponentEquiv d.vertexGraph))
    ((S.orderIsoOfFin rfl).toEquiv)).2

/-- An arbitrary component shuffle with canonical increasing local
vertex orders is exactly a relabeling of the canonical global vertex
order. The relabeling changes only the interleaving, not the ordered
slots inside a connected component; no individual Dyson integral
invariance is asserted. -/
theorem ExternalInsertionDiagram.assembleInteractionOrder_eq_canonicalRelabel
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (ρ : d.ComponentInteractionOrderShuffle) :
    d.assembleInteractionOrder d.canonicalComponentInteractionOrders ρ =
      (d.canonicalComponentInteractionShuffle.ambientRelabel ρ).symm.trans
        (S.orderIsoOfFin rfl).toEquiv := by
  classical
  let family : d.vertexGraph.componentPartition.parts → Type :=
    fun B => ↥(interactionSector (B : Finset (ExternalInsertionVertex E S)))
  let size : d.vertexGraph.componentPartition.parts → ℕ :=
    fun B => (interactionSector (B : Finset (ExternalInsertionVertex E S))).card
  let ambient := interactionSectorComponentEquiv d.vertexGraph
  let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
  let e := familyOrderDecompositionEquivOfSize family size
    (fun _ => by simp) ambient
  have hmono (B : d.vertexGraph.componentPartition.parts) :
      StrictMono (fun j : Fin (size B) =>
        order.symm (ambient.symm ⟨B, d.canonicalComponentInteractionOrders B j⟩)) := by
    intro a b hab
    apply (S.orderIsoOfFin rfl).symm.strictMono
    change (ambient.symm ⟨B, d.canonicalComponentInteractionOrders B a⟩).1 <
      (ambient.symm ⟨B, d.canonicalComponentInteractionOrders B b⟩).1
    rw [interactionSectorComponentEquiv_symm_val,
      interactionSectorComponentEquiv_symm_val]
    exact ((interactionSector (B : Finset (ExternalInsertionVertex E S))).orderIsoOfFin
      rfl).strictMono hab
  have hlocal : (e order).1 = d.canonicalComponentInteractionOrders := by
    change familyOrdersOfOrder family size (fun _ => by simp) ambient order =
      d.canonicalComponentInteractionOrders
    exact familyOrdersOfOrder_eq_of_strictMono family size (fun _ => by simp)
      ambient order d.canonicalComponentInteractionOrders hmono
  have hbase :
      d.assembleInteractionOrder d.canonicalComponentInteractionOrders
        d.canonicalComponentInteractionShuffle = order := by
    have h := e.symm_apply_apply order
    change assembleFamilyOrderOfSize family size ambient (e order).1
      (e order).2 = order at h
    change assembleFamilyOrderOfSize family size ambient
      d.canonicalComponentInteractionOrders (e order).2 = order
    rw [← hlocal]
    exact h
  have hrelab := assembleFamilyOrderOfSize_ambientRelabel family size ambient
    d.canonicalComponentInteractionOrders
    d.canonicalComponentInteractionShuffle ρ
  change (assembleFamilyOrderOfSize family size ambient
      d.canonicalComponentInteractionOrders ρ) =
      (d.canonicalComponentInteractionShuffle.ambientRelabel ρ).symm.trans order
  rw [← hbase]
  exact hrelab.symm

/-- The owner of an ambient canonical interaction slot under the
canonical component shuffle is precisely its *actual graph component*.
This is the ownership identity needed to compare a physical owner
assignment with the graph-component shuffle, without modifying any
local vertex numbering. -/
theorem ExternalInsertionDiagram.canonicalComponentInteractionShuffle_owner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (v : Fin S.card) :
    (d.canonicalComponentInteractionShuffle.slotEquiv.symm v).1 =
      (interactionSectorComponentEquiv d.vertexGraph
        ((S.orderIsoOfFin rfl).toEquiv v)).1 := by
  classical
  let σ := d.canonicalComponentInteractionShuffle
  let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
  have hglobal : d.assembleInteractionOrder
      d.canonicalComponentInteractionOrders σ = order := by
    simpa [σ, order, FamilySlotShuffleTo.ambientRelabel] using
      d.assembleInteractionOrder_eq_canonicalRelabel σ
  rcases hslot : σ.slotEquiv.symm v with ⟨C, j⟩
  have hback : σ.slotEquiv ⟨C, j⟩ = v := by
    calc
      σ.slotEquiv ⟨C, j⟩ = σ.slotEquiv (σ.slotEquiv.symm v) :=
        congrArg σ.slotEquiv hslot.symm
      _ = v := σ.slotEquiv.apply_symm_apply v
  have hlocal := d.assembleInteractionOrder_symm_apply
    d.canonicalComponentInteractionOrders σ C j
  rw [hglobal, hback] at hlocal
  have hvertex :
      order v = (interactionSectorComponentEquiv d.vertexGraph).symm
        ⟨C, d.canonicalComponentInteractionOrders C j⟩ := by
    apply Subtype.ext
    have h := congrArg order hlocal
    simpa only [Equiv.apply_symm_apply, interactionSectorComponentEquiv_symm_val]
      using congrArg Subtype.val h.symm
  have howner :
      (interactionSectorComponentEquiv d.vertexGraph (order v)).1 = C := by
    rw [hvertex]
    simp
  simpa only [hslot] using howner.symm

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
  have hsP : (∑ P, size (e.symm P)) = S.card :=
    d.sum_externalBlockInteractionSector_card_eq hVac
  exact
    ((FamilySlotShuffleTo.castTotalEquiv hs.symm).trans
      (FamilySlotShuffle.reindexEquiv e.symm size)).trans
      (FamilySlotShuffleTo.castTotalEquiv hsP)


end Common
end SecondQuantization
