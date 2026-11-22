import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockRestrictionEquiv

set_option linter.style.header false

/-!
# Physical reconstruction of external block layouts

The layout extracted from a vacuum-free physical diagram, and proofs that
canonical connected components reconstruct the original physical diagram.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

/-- A vacuum-free *physical* external-insertion diagram canonically determines
an independent external-block layout. For occupied interaction vertices the
owner is their actual graph component, transported to the external partition.
The anchor supplies an arbitrary default owner only for vertices outside
the active interaction set; none of these vertices enters the diagram. -/
noncomputable def ExternalInsertionDiagram.externalBlockLayout
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) : ExternalInsertionBlockLayout E N where
  partition := externalComponentPartition d.vertexGraph
  evenBlocks := fun B =>
    d.externalComponentPartition_block_card_even B.1 B.2
  interactionOwner := fun v =>
    if hv : v ∈ S then
      d.vacuumFreeComponentsEquivExternalBlocks hVac
        ⟨d.vertexGraph.componentBlock (Sum.inr (⟨v, hv⟩ : ↥S)),
          d.vertexGraph.componentBlock_mem_componentPartition
            (Sum.inr (⟨v, hv⟩ : ↥S))⟩
    else
      ⟨(externalComponentPartition d.vertexGraph).part anchor,
        (externalComponentPartition d.vertexGraph).part_mem.2
          (Finset.mem_univ anchor)⟩

/-- The constructed layout uses the exact physical external-component
partition, with no coarsening or formal proxy partition. -/
@[simp]
theorem ExternalInsertionDiagram.externalBlockLayout_partition
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) :
    (d.externalBlockLayout hVac anchor).partition =
      externalComponentPartition d.vertexGraph := rfl

/-- On active interaction vertices the layout assignment is the unique
actual connected component, identified with its external block. -/
theorem ExternalInsertionDiagram.externalBlockLayout_interactionOwner
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) (v : ↥S) :
    (d.externalBlockLayout hVac anchor).interactionOwner v.1 =
      d.vacuumFreeComponentsEquivExternalBlocks hVac
        ⟨d.vertexGraph.componentBlock (Sum.inr v),
          d.vertexGraph.componentBlock_mem_componentPartition (Sum.inr v)⟩ := by
  simp [ExternalInsertionDiagram.externalBlockLayout, v.2]

/-- If an external insertion reaches an interaction vertex, the latter's
assigned block is exactly the external partition part of that insertion.
This gives the physical ownership direction needed by fiber restriction. -/
theorem ExternalInsertionDiagram.externalBlockLayout_owner_eq_part_of_reachable
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) (v : ↥S) (e : Fin (2 * E))
    (h : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr v)) :
    ((d.externalBlockLayout hVac anchor).interactionOwner v.1).1 =
      (externalComponentPartition d.vertexGraph).part e := by
  rw [d.externalBlockLayout_interactionOwner hVac anchor v]
  calc
    _ = (d.vertexGraph.componentBlock (Sum.inr v)).toLeft :=
      d.vacuumFreeComponentsEquivExternalBlocks_apply hVac _
    _ = (d.vertexGraph.componentBlock (Sum.inl e)).toLeft :=
      congrArg Finset.toLeft (d.vertexGraph.componentBlock_eq_of_reachable h.symm)
    _ = _ := (d.externalComponentPartition_part_eq_toLeft_componentBlock e).symm



/-- The interaction sector of an independently indexed physical block is
*exactly* the interaction sector of the corresponding actual connected
component. Thus the interaction assignment in the physical layout is not
additional combinatorial data. -/
theorem ExternalInsertionDiagram.externalBlockLayout_interactionBlock
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E))
    (P : (externalComponentPartition d.vertexGraph).parts) :
    (d.externalBlockLayout hVac anchor).interactionBlock S P =
      interactionSector
        (((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P).1 :
          Finset (ExternalInsertionVertex E S)) := by
  classical
  let equiv := d.vacuumFreeComponentsEquivExternalBlocks hVac
  ext v
  constructor
  · intro hv
    have hfilter : v ∈ S ∧
        (d.externalBlockLayout hVac anchor).interactionOwner v = P := by
      simpa only [ExternalInsertionBlockLayout.interactionBlock,
        Finset.mem_filter] using hv
    let V : ↥S := ⟨v, hfilter.1⟩
    let C : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inr V),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inr V)⟩
    have howner : equiv C = P := by
      have heq : (d.externalBlockLayout hVac anchor).interactionOwner V.1 = P :=
        hfilter.2
      rw [d.externalBlockLayout_interactionOwner hVac anchor V] at heq
      exact heq
    have hC : C = equiv.symm P := by
      apply equiv.injective
      simpa only [howner, Equiv.apply_symm_apply]
    apply (mem_interactionSector_subtype
      ((equiv.symm P).1 : Finset (ExternalInsertionVertex E S)) V).2
    have hmem : (Sum.inr V : ExternalInsertionVertex E S) ∈
        (C.1 : Finset (ExternalInsertionVertex E S)) :=
      d.vertexGraph.self_mem_componentBlock (Sum.inr V)
    simpa only [hC] using hmem
  · intro hv
    have hvS : v ∈ S :=
      interactionSector_subset
        (((equiv.symm P).1 : Finset (ExternalInsertionVertex E S))) hv
    let V : ↥S := ⟨v, hvS⟩
    let C : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inr V),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inr V)⟩
    have hmem : (Sum.inr V : ExternalInsertionVertex E S) ∈
        ((equiv.symm P).1 : Finset (ExternalInsertionVertex E S)) :=
      (mem_interactionSector_subtype
        ((equiv.symm P).1 : Finset (ExternalInsertionVertex E S)) V).1 hv
    have hC : C = equiv.symm P := by
      apply Subtype.ext
      exact (d.vertexGraph.componentBlock_eq_iff_mem
        (equiv.symm P).2 (Sum.inr V)).2 hmem
    have howner :
        (d.externalBlockLayout hVac anchor).interactionOwner V.1 = P := by
      rw [d.externalBlockLayout_interactionOwner hVac anchor V]
      change equiv C = P
      rw [hC, Equiv.apply_symm_apply]
    simpa only [ExternalInsertionBlockLayout.interactionBlock,
      Finset.mem_filter] using (show v ∈ S ∧
      (d.externalBlockLayout hVac anchor).interactionOwner v = P from
        ⟨hvS, howner⟩)


/-- The external block owner of every physical vertex is precisely the
external support of its actual graph component. This includes occupied
quartic interaction vertices, not just external source insertions. -/
theorem ExternalInsertionDiagram.externalBlockLayout_vertexPart
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) (v : ExternalInsertionVertex E S) :
    (((d.externalBlockLayout hVac anchor).vertexEquiv S v).1 :
      Finset (Fin (2 * E))) = (d.vertexGraph.componentBlock v).toLeft := by
  cases v with
  | inl e =>
      change (d.externalBlockLayout hVac anchor).partition.part e =
        (d.vertexGraph.componentBlock (Sum.inl e)).toLeft
      exact d.externalComponentPartition_part_eq_toLeft_componentBlock e
  | inr w =>
      change ((d.externalBlockLayout hVac anchor).interactionOwner w.1).1 =
        (d.vertexGraph.componentBlock (Sum.inr w)).toLeft
      rw [d.externalBlockLayout_interactionOwner hVac anchor w]
      exact d.vacuumFreeComponentsEquivExternalBlocks_apply hVac _

/-- In a vacuum-free physical diagram, two vertices are reachable
precisely when their canonical external-block owners agree. This uses the
injectivity of the equivalence between actual graph components and external
partition parts, rather than assuming equal external support determines
connectivity for arbitrary graphs. -/
theorem ExternalInsertionDiagram.reachable_iff_externalBlockLayout_same_block
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) (v w : ExternalInsertionVertex E S) :
    d.vertexGraph.Reachable v w ↔
      ((d.externalBlockLayout hVac anchor).vertexEquiv S v).1 =
        ((d.externalBlockLayout hVac anchor).vertexEquiv S w).1 := by
  constructor
  · intro h
    apply Subtype.ext
    calc
      (((d.externalBlockLayout hVac anchor).vertexEquiv S v).1 :
          Finset (Fin (2 * E))) =
          (d.vertexGraph.componentBlock v).toLeft :=
        d.externalBlockLayout_vertexPart hVac anchor v
      _ = (d.vertexGraph.componentBlock w).toLeft :=
        congrArg Finset.toLeft (d.vertexGraph.componentBlock_eq_of_reachable h)
      _ = (((d.externalBlockLayout hVac anchor).vertexEquiv S w).1 :
          Finset (Fin (2 * E))) :=
        (d.externalBlockLayout_vertexPart hVac anchor w).symm
  · intro h
    have hBlocks : (d.vertexGraph.componentBlock v).toLeft =
        (d.vertexGraph.componentBlock w).toLeft := by
      calc
        _ = (((d.externalBlockLayout hVac anchor).vertexEquiv S v).1 :
            Finset (Fin (2 * E))) :=
          (d.externalBlockLayout_vertexPart hVac anchor v).symm
        _ = (((d.externalBlockLayout hVac anchor).vertexEquiv S w).1 :
            Finset (Fin (2 * E))) := congrArg Subtype.val h
        _ = _ := d.externalBlockLayout_vertexPart hVac anchor w
    have hEquiv :
        d.vacuumFreeComponentsEquivExternalBlocks hVac
            ⟨d.vertexGraph.componentBlock v,
              d.vertexGraph.componentBlock_mem_componentPartition v⟩ =
          d.vacuumFreeComponentsEquivExternalBlocks hVac
            ⟨d.vertexGraph.componentBlock w,
              d.vertexGraph.componentBlock_mem_componentPartition w⟩ := by
      apply Subtype.ext
      calc
        _ = (d.vertexGraph.componentBlock v).toLeft :=
          d.vacuumFreeComponentsEquivExternalBlocks_apply hVac _
        _ = (d.vertexGraph.componentBlock w).toLeft := hBlocks
        _ = _ :=
          (d.vacuumFreeComponentsEquivExternalBlocks_apply hVac
            ⟨d.vertexGraph.componentBlock w,
              d.vertexGraph.componentBlock_mem_componentPartition w⟩).symm
    have hComp : d.vertexGraph.componentBlock v =
        d.vertexGraph.componentBlock w :=
      congrArg Subtype.val
        ((d.vacuumFreeComponentsEquivExternalBlocks hVac).injective hEquiv)
    exact (d.vertexGraph.componentBlock_eq_iff_reachable v w).mp hComp

/-- The physical component layout does not split a paired propagator
between external blocks: both endpoints of every pair lie in the
same actual graph component, hence in its same external block. -/
theorem ExternalInsertionDiagram.externalBlockLayout_partner_block
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E))
    (leg : Fin (2 * (2 * S.card + E))) :
    ((d.externalBlockLayout hVac anchor).legEquiv S
      (d.pairing.partner leg)).1 =
      ((d.externalBlockLayout hVac anchor).legEquiv S leg).1 := by
  let layout := d.externalBlockLayout hVac anchor
  apply Subtype.ext
  calc
    ((layout.legEquiv S (d.pairing.partner leg)).1 : Finset (Fin (2 * E))) =
        ((layout.vertexEquiv S
          (externalInsertionVertexOfLeg (d.pairing.partner leg))).1 :
          Finset (Fin (2 * E))) :=
      (congrArg Subtype.val
        (congrArg Sigma.fst
          (layout.vertexEquiv_vertexOfLeg S (d.pairing.partner leg)))).symm
    _ = (d.vertexGraph.componentBlock
          (externalInsertionVertexOfLeg (d.pairing.partner leg))).toLeft :=
      d.externalBlockLayout_vertexPart hVac anchor _
    _ = (d.vertexGraph.componentBlock
          (externalInsertionVertexOfLeg leg)).toLeft :=
      congrArg Finset.toLeft
        (d.pairing.vertexGraph_componentBlock_partner
          (externalInsertionVertexOfLeg (E := E)) leg).symm
    _ = ((layout.vertexEquiv S (externalInsertionVertexOfLeg leg)).1 :
          Finset (Fin (2 * E))) :=
      (d.externalBlockLayout_vertexPart hVac anchor _).symm
    _ = ((layout.legEquiv S leg).1 : Finset (Fin (2 * E))) :=
      congrArg Subtype.val
        (congrArg Sigma.fst (layout.vertexEquiv_vertexOfLeg S leg))

/-- The actual graph-component partition of a vacuum-free diagram gives a
physical block layout whose restricted local diagrams reassemble to the
*same labelled diagram and pairing*, not just an equal partition. -/
theorem ExternalInsertionDiagram.assembleDiagram_restrictPhysicalBlocks
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) :
    (d.externalBlockLayout hVac anchor).assembleDiagram S
      ((d.externalBlockLayout hVac anchor).restrictBlock S d
        (d.externalBlockLayout_partner_block hVac anchor)) = d :=
  (d.externalBlockLayout hVac anchor).assembleDiagram_restrictBlock S d
    (d.externalBlockLayout_partner_block hVac anchor)

/-- Every block extracted from a vacuum-free physical diagram is
preconnected in its own vertex graph. The proof reflects actual physical
paths through the assembly/restriction round trip; it does not postulate
local connectivity as an extra assumption. -/
theorem ExternalInsertionDiagram.restrictPhysicalBlocks_preconnected
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E))
    (B : (d.externalBlockLayout hVac anchor).partition.parts) :
    ((d.externalBlockLayout hVac anchor).restrictBlock S d
      (d.externalBlockLayout_partner_block hVac anchor) B).vertexGraph.Preconnected := by
  let layout := d.externalBlockLayout hVac anchor
  let F := layout.restrictBlock S d
    (d.externalBlockLayout_partner_block hVac anchor)
  have hRound : layout.assembleDiagram S F = d :=
    d.assembleDiagram_restrictPhysicalBlocks hVac anchor
  intro u v
  apply (layout.blockGraphHom_reachable_iff S F B u v).2
  rw [hRound]
  apply (d.reachable_iff_externalBlockLayout_same_block hVac anchor _ _).2
  change (layout.vertexEquiv S
      ((layout.vertexEquiv S).symm ⟨B, u⟩)).1 =
    (layout.vertexEquiv S
      ((layout.vertexEquiv S).symm ⟨B, v⟩)).1
  simp



/-- Constructive decomposition of every vacuum-free physical diagram
(with a chosen external anchor) into a family of *preconnected* local
diagrams over its actual external-component partition. Their exact
independent assembly returns the original diagram, including labels
and Wick-pairing partners. This establishes the diagram-level
surjectivity needed before summing Dyson amplitudes over fibers. -/
theorem ExternalInsertionDiagram.exists_preconnectedPhysicalBlockAssembly
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) :
    ∃ F : ∀ B : (d.externalBlockLayout hVac anchor).partition.parts,
        ExternalInsertionDiagram ExternalLabel InternalLabel
          ((B : Finset (Fin (2 * E))).card / 2) N
          ((d.externalBlockLayout hVac anchor).interactionBlock S B),
      (∀ B, (F B).vertexGraph.Preconnected) ∧
        (d.externalBlockLayout hVac anchor).assembleDiagram S F = d := by
  refine ⟨(d.externalBlockLayout hVac anchor).restrictBlock S d
    (d.externalBlockLayout_partner_block hVac anchor), ?_, ?_⟩
  · exact d.restrictPhysicalBlocks_preconnected hVac anchor
  · exact d.assembleDiagram_restrictPhysicalBlocks hVac anchor



/-- For an assembly of connected local diagrams, extracting the physical
external-component layout recovers the originally assigned block of every
*active* interaction vertex. An assignment on inactive ambient vertices is
irrelevant; at full interaction order there are no inactive vertices. -/
theorem ExternalInsertionBlockLayout.externalBlockLayout_assembleDiagram_interactionOwner
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (anchor : Fin (2 * E)) (v : ↥S) :
    (((layout.assembleDiagram S F).externalBlockLayout
        (layout.hasNoVacuumComponent_assembleDiagram S F hconnected) anchor).interactionOwner v.1 :
          Finset (Fin (2 * E))) =
      (layout.interactionOwner v.1 : Finset (Fin (2 * E))) := by
  let B : layout.partition.parts := layout.interactionOwner v.1
  have hnonempty : (B : Finset (Fin (2 * E))).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (layout.partition.ne_bot B.2)
  obtain ⟨e, he⟩ := hnonempty
  have hsource : (layout.sourceEquiv e).1 = B := by
    apply Subtype.ext
    simpa only [layout.sourceEquiv_fst] using
      (layout.partition.part_eq_of_mem B.2 he)
  have hinteraction : (layout.interactionEquiv S v).1 = B := by
    rfl
  have hReach :
      (layout.assembleDiagram S F).vertexGraph.Reachable (Sum.inl e) (Sum.inr v) := by
    apply (layout.assembleDiagram_reachable_iff_same_block S F hconnected
      (Sum.inl e) (Sum.inr v)).2
    simpa only [layout.vertexEquiv_external, layout.vertexEquiv_interaction] using
      hsource.trans hinteraction.symm
  calc
    (((layout.assembleDiagram S F).externalBlockLayout
        (layout.hasNoVacuumComponent_assembleDiagram S F hconnected) anchor).interactionOwner v.1 :
          Finset (Fin (2 * E))) =
        (externalComponentPartition (layout.assembleDiagram S F).vertexGraph).part e :=
      (layout.assembleDiagram S F).externalBlockLayout_owner_eq_part_of_reachable
        (layout.hasNoVacuumComponent_assembleDiagram S F hconnected) anchor v e hReach
    _ = layout.partition.part e := by
      rw [layout.externalComponentPartition_assembleDiagram S F hconnected]
    _ = (layout.interactionOwner v.1 : Finset (Fin (2 * E))) := by
      exact layout.partition.part_eq_of_mem B.2 he

end Common
end SecondQuantization
