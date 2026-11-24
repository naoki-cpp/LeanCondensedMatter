import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.InteractionOrder

set_option linter.style.header false

/-!
# Interaction-order decompositions for external blocks

Canonical shuffles of ambient quartic-vertex orders and recovery of the
physical block assignment from fully assembled connected components.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

/-- Reindex a vacuum-free diagram's actual graph-component
interaction shuffles by the physical interaction-owner fibers of its
canonical external block layout. This composes the existing component
reindexing with the proved equality of each physical interaction block
and graph interaction sector, without introducing additional orders. -/
noncomputable def ExternalInsertionDiagram.physicalBlockInteractionShuffleEquiv
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) :
    d.ComponentInteractionOrderShuffle ≃
      FamilySlotShuffleTo
        (fun P : (d.externalBlockLayout hVac anchor).partition.parts =>
          ((d.externalBlockLayout hVac anchor).interactionBlock S P).card)
        S.card := by
  classical
  let e := d.vacuumFreeComponentsEquivExternalBlocks hVac
  let f : d.vertexGraph.componentPartition.parts → ℕ :=
    fun C => (interactionSector
      (C : Finset (ExternalInsertionVertex E S))).card
  let g : (externalComponentPartition d.vertexGraph).parts → ℕ :=
    fun P => ((d.externalBlockLayout hVac anchor).interactionBlock S P).card
  have hfg : (fun P => f (e.symm P)) = g := by
    funext P
    exact (congrArg Finset.card
      (d.externalBlockLayout_interactionBlock hVac anchor P)).symm
  exact (FamilySlotShuffleTo.reindexEquiv (total := S.card) e.symm f).trans
    (Equiv.cast (congrArg (fun s => FamilySlotShuffleTo s S.card) hfg))

/-- Reindexing component shuffles by the *actual physical* external
blocks preserves the ambient interaction-time permutation between any
two interleavings. No local order or numerical time is changed. -/
theorem ExternalInsertionDiagram.physicalBlockInteractionShuffleEquiv_ambientRelabel
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E))
    (ρ τ : d.ComponentInteractionOrderShuffle) :
    ((d.physicalBlockInteractionShuffleEquiv hVac anchor) ρ).ambientRelabel
        ((d.physicalBlockInteractionShuffleEquiv hVac anchor) τ) =
      ρ.ambientRelabel τ := by
  classical
  let e := d.vacuumFreeComponentsEquivExternalBlocks hVac
  let f : d.vertexGraph.componentPartition.parts → ℕ :=
    fun C => (interactionSector
      (C : Finset (ExternalInsertionVertex E S))).card
  let g : (externalComponentPartition d.vertexGraph).parts → ℕ :=
    fun P => ((d.externalBlockLayout hVac anchor).interactionBlock S P).card
  have hfg : (fun P => f (e.symm P)) = g := by
    funext P
    exact (congrArg Finset.card
      (d.externalBlockLayout_interactionBlock hVac anchor P)).symm
  let rename := FamilySlotShuffleTo.reindexEquiv (total := S.card) e.symm f
  let cast : FamilySlotShuffleTo (fun P => f (e.symm P)) S.card ≃
      FamilySlotShuffleTo g S.card :=
    Equiv.cast (congrArg (fun s => FamilySlotShuffleTo s S.card) hfg)
  have hcast :
      ((cast (rename ρ)).ambientRelabel (cast (rename τ))) =
        (rename ρ).ambientRelabel (rename τ) :=
    FamilySlotShuffleTo.castSize_ambientRelabel hfg (rename ρ) (rename τ)
  calc
    _ = (rename ρ).ambientRelabel (rename τ) := by
      change (cast (rename ρ)).ambientRelabel (cast (rename τ)) = _
      exact hcast
    _ = _ := FamilySlotShuffleTo.reindexEquiv_ambientRelabel e.symm f ρ τ

/-- The actual physical owner of an ambient slot in a component shuffle
is the external-partition block of the graph component owning that slot. -/
theorem ExternalInsertionDiagram.physicalBlockInteractionShuffleEquiv_owner
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E))
    (ρ : d.ComponentInteractionOrderShuffle) (v : Fin S.card) :
    (((d.physicalBlockInteractionShuffleEquiv hVac anchor) ρ).slotEquiv.symm v).1 =
      d.vacuumFreeComponentsEquivExternalBlocks hVac
        (ρ.slotEquiv.symm v).1 := by
  classical
  let e := d.vacuumFreeComponentsEquivExternalBlocks hVac
  let f : d.vertexGraph.componentPartition.parts → ℕ :=
    fun C => (interactionSector
      (C : Finset (ExternalInsertionVertex E S))).card
  let g : (externalComponentPartition d.vertexGraph).parts → ℕ :=
    fun P => ((d.externalBlockLayout hVac anchor).interactionBlock S P).card
  have hfg : (fun P => f (e.symm P)) = g := by
    funext P
    exact (congrArg Finset.card
      (d.externalBlockLayout_interactionBlock hVac anchor P)).symm
  let rename := FamilySlotShuffleTo.reindexEquiv (total := S.card) e.symm f
  let cast : FamilySlotShuffleTo (fun P => f (e.symm P)) S.card ≃
      FamilySlotShuffleTo g S.card :=
    Equiv.cast (congrArg (fun s => FamilySlotShuffleTo s S.card) hfg)
  have hcast :
      ((cast (rename ρ)).slotEquiv.symm v).1 =
        ((rename ρ).slotEquiv.symm v).1 :=
    FamilySlotShuffleTo.castSize_owner hfg (rename ρ) v
  change ((cast (rename ρ)).slotEquiv.symm v).1 = _
  rw [hcast]
  exact FamilySlotShuffleTo.reindexEquiv_owner e.symm f ρ v

/-- The canonical graph-component shuffle of a vacuum-free physical
diagram has exactly the interaction owner prescribed by its physical
external-block layout at each ambient vertex position. -/
theorem ExternalInsertionDiagram.canonicalComponentInteractionShuffle_physicalOwner
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) (v : Fin S.card) :
    d.vacuumFreeComponentsEquivExternalBlocks hVac
        (d.canonicalComponentInteractionShuffle.slotEquiv.symm v).1 =
      (d.externalBlockLayout hVac anchor).interactionOwner
        (((S.orderIsoOfFin rfl).toEquiv v).1) := by
  classical
  let w : ↥S := (S.orderIsoOfFin rfl).toEquiv v
  have hC :
      (interactionSectorComponentEquiv d.vertexGraph w).1 =
        ⟨d.vertexGraph.componentBlock (Sum.inr w),
          d.vertexGraph.componentBlock_mem_componentPartition (Sum.inr w)⟩ := by
    apply Subtype.ext
    exact interactionSectorComponentEquiv_fst d.vertexGraph w
  rw [d.canonicalComponentInteractionShuffle_owner v, hC]
  exact (d.externalBlockLayout_interactionOwner hVac anchor w).symm

/-- Every global interaction-vertex order decomposes uniquely into one
local order for each independently assigned external block and an
order-preserving shuffle of those local slots. In particular, blocks
with no interaction vertices retain their unique empty local order. -/
noncomputable def ExternalInsertionBlockLayout.interactionOrderDecompositionEquiv
    (layout : ExternalInsertionBlockLayout E N) :
    QuarticVertexOrder (Finset.univ : Finset (Fin N)) ≃
      FamilyOrdersOf
        (fun B : layout.partition.parts =>
          ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
        (fun B => (layout.interactionBlock
          (Finset.univ : Finset (Fin N)) B).card) ×
      FamilySlotShuffleTo
        (fun B : layout.partition.parts =>
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
        (Finset.univ : Finset (Fin N)).card := by
  classical
  exact familyOrderDecompositionEquivOfSize
    (fun B : layout.partition.parts =>
      ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (fun B => (layout.interactionBlock
      (Finset.univ : Finset (Fin N)) B).card)
    (fun B => by simp)
    (layout.interactionEquiv (Finset.univ : Finset (Fin N)))

/-- The interaction vertex at each shuffled global slot is exactly
the vertex identified by the corresponding local block order. The
ambient order is arbitrary, so this applies to the actual ordered Dyson
integrand, not just the canonical increasing vertex order. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_slotVertex
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩) =
      (layout.interactionEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (layout.interactionOrderDecompositionEquiv order).1 B j⟩ := by
  classical
  let e := layout.interactionOrderDecompositionEquiv
  let data := e order
  let family : layout.partition.parts → Type :=
    fun C => ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) C)
  let size : layout.partition.parts → ℕ :=
    fun C => (layout.interactionBlock (Finset.univ : Finset (Fin N)) C).card
  let ambient := layout.interactionEquiv (Finset.univ : Finset (Fin N))
  have hassemble :
      assembleFamilyOrderOfSize family size ambient data.1 data.2 = order :=
    e.symm_apply_apply order
  change order (data.2.slotEquiv ⟨B, j⟩) =
    ambient.symm ⟨B, data.1 B j⟩
  calc
    order (data.2.slotEquiv ⟨B, j⟩) =
      (assembleFamilyOrderOfSize family size ambient data.1 data.2)
        (data.2.slotEquiv ⟨B, j⟩) := by rw [hassemble]
    _ = ambient.symm ⟨B, data.1 B j⟩ :=
      assembleFamilyOrderOfSize_slot family size ambient data.1 data.2 B j

/-- Every shuffled slot in an arbitrary global interaction order belongs
to its specified physical external-source block; interleavings cannot
move quartic vertices across assigned blocks. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_slot_owner
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    layout.interactionOwner
      (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩)).1 = B := by
  classical
  rw [layout.interactionOrderDecomposition_slotVertex order B j]
  let v := (layout.interactionOrderDecompositionEquiv order).1 B j
  have hfst :=
    congrArg Sigma.fst
      ((layout.interactionEquiv (Finset.univ : Finset (Fin N))).apply_symm_apply
        (⟨B, v⟩ : Σ C : layout.partition.parts,
          ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) C)))
  change layout.interactionOwner
    ((layout.interactionEquiv (Finset.univ : Finset (Fin N))).symm ⟨B, v⟩).1 = B at hfst
  exact hfst

/-- For an *arbitrary* global interaction-time order, the inverse
order-preserving shuffle recovers the true physical owner of the vertex
occupying each ordered-simplex slot. This is stronger than the canonical
assignment-shuffle statement: it simultaneously handles every local
interaction order and interleaving, including empty blocks. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_owner
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (v : Fin (Finset.univ : Finset (Fin N)).card) :
    ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv.symm v).1 =
      layout.interactionOwner (order v).1 := by
  classical
  let σ := (layout.interactionOrderDecompositionEquiv order).2
  rcases hslot : σ.slotEquiv.symm v with ⟨B, j⟩
  have hback : σ.slotEquiv ⟨B, j⟩ = v := by
    calc
      σ.slotEquiv ⟨B, j⟩ =
          σ.slotEquiv (σ.slotEquiv.symm v) :=
        congrArg σ.slotEquiv hslot.symm
      _ = v := σ.slotEquiv.apply_symm_apply v
  have howner := layout.interactionOrderDecomposition_slot_owner order B j
  change layout.interactionOwner (order (σ.slotEquiv ⟨B, j⟩)).1 = B at howner
  simpa only [hback] using howner.symm

/-- Extract the canonical interaction-slot shuffle of an independently
assigned external-block layout from the already proved global-order
decomposition. This retains all zero-size interaction fibers and avoids
a second dependent enumeration of owner subtypes. -/
noncomputable def ExternalInsertionBlockLayout.interactionAssignmentShuffle
    (layout : ExternalInsertionBlockLayout E N) :
    FamilySlotShuffleTo
      (fun B : layout.partition.parts =>
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
      (Finset.univ : Finset (Fin N)).card :=
  (layout.interactionOrderDecompositionEquiv
    ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv).2

/-- The canonical component interleaving of a vacuum-free physical
diagram becomes exactly the canonical interaction-assignment shuffle
of its true external-block layout. This is a consequence of the
*physical owner* identity and uniqueness of increasing family shuffles,
not a new combinatorial enumeration. -/
theorem ExternalInsertionDiagram.physicalBlockInteractionShuffleEquiv_canonical
    {ExternalLabel InternalLabel : Type*}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)))
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) :
    (d.physicalBlockInteractionShuffleEquiv hVac anchor)
        d.canonicalComponentInteractionShuffle =
      (d.externalBlockLayout hVac anchor).interactionAssignmentShuffle := by
  classical
  apply FamilySlotShuffleTo.eq_of_same_owner
  intro v
  rw [d.physicalBlockInteractionShuffleEquiv_owner
    hVac anchor d.canonicalComponentInteractionShuffle v]
  rw [d.canonicalComponentInteractionShuffle_physicalOwner hVac anchor v]
  exact ((d.externalBlockLayout hVac anchor).interactionOrderDecomposition_owner
    ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv v).symm

/-- The component-order Dyson orbit of a genuine vacuum-free diagram
uses precisely the transported global orders of the *physical*
interaction-assignment shuffles. The identity is pointwise in the
shuffle, including empty local interaction blocks, so it preserves the
entire signed ordered-simplex amplitude. -/
theorem ExternalInsertionDiagram.assembleInteractionOrder_eq_physicalOwnerRelabel
    {ExternalLabel InternalLabel : Type*}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)))
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E))
    (ρ : d.ComponentInteractionOrderShuffle) :
    d.assembleInteractionOrder d.canonicalComponentInteractionOrders ρ =
      (((d.externalBlockLayout hVac anchor).interactionAssignmentShuffle.ambientRelabel
        ((d.physicalBlockInteractionShuffleEquiv hVac anchor) ρ)).symm.trans
          ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv) := by
  classical
  have hrelab := d.physicalBlockInteractionShuffleEquiv_ambientRelabel
    hVac anchor d.canonicalComponentInteractionShuffle ρ
  rw [d.physicalBlockInteractionShuffleEquiv_canonical hVac anchor] at hrelab
  calc
    _ = (d.canonicalComponentInteractionShuffle.ambientRelabel ρ).symm.trans
          ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv :=
      d.assembleInteractionOrder_eq_canonicalRelabel ρ
    _ = _ := by
      rw [← hrelab]

/-- Two external block layouts are equal if their source partitions and
underlying interaction-owner blocks coincide. The evenness witnesses are
propositions, so they carry no additional data. -/
theorem ExternalInsertionBlockLayout.ext_of_partition_owner
    {left right : ExternalInsertionBlockLayout E N}
    (hpart : left.partition = right.partition)
    (howner : ∀ v : Fin N,
      (left.interactionOwner v : Finset (Fin (2 * E))) =
        (right.interactionOwner v : Finset (Fin (2 * E)))) :
    left = right := by
  cases left with
  | mk π heven owner =>
    cases right with
    | mk ρ heven' owner' =>
      dsimp at hpart
      cases hpart
      have hfunc : owner = owner' := by
        funext v
        exact Subtype.ext (howner v)
      cases hfunc
      rfl

/-- At full interaction order, reconstructing the physical connected
components of an independently assembled family of preconnected local
diagrams recovers its *entire original layout*, not just the external
partition or individual active interaction owners. -/
theorem ExternalInsertionBlockLayout.externalBlockLayout_assembleDiagram_eq
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (anchor : Fin (2 * E)) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).externalBlockLayout
        (layout.hasNoVacuumComponent_assembleDiagram
          (Finset.univ : Finset (Fin N)) F hconnected) anchor = layout := by
  apply ExternalInsertionBlockLayout.ext_of_partition_owner
  · exact layout.externalComponentPartition_assembleDiagram
      (Finset.univ : Finset (Fin N)) F hconnected
  · intro v
    exact layout.externalBlockLayout_assembleDiagram_interactionOwner
      (Finset.univ : Finset (Fin N)) F hconnected anchor
      ⟨v, Finset.mem_univ v⟩



/-- The physical block layout depends only on the labelled diagram,
not on which proof of absence of vacuum components is supplied. -/
theorem ExternalInsertionDiagram.externalBlockLayout_congr
    {ExternalLabel InternalLabel : Type*}
    {d e : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N))}
    (h : d = e)
    (hVacD : HasNoVacuumComponent d.vertexGraph)
    (hVacE : HasNoVacuumComponent e.vertexGraph)
    (anchor : Fin (2 * E)) :
    d.externalBlockLayout hVacD anchor = e.externalBlockLayout hVacE anchor := by
  subst e
  rfl


end Common
end SecondQuantization
