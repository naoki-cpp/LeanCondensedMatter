import Mathlib.Logic.Equiv.Basic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockLayout
import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Connectivity and restriction of assembled external-insertion blocks

Physical graph-component recovery, canonical leg and pairing restriction, and
reconstruction from block-respecting labelled diagrams.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

/-- A propagator in the assembled physical vertex graph cannot connect
different source-partition blocks, independently of whether the local graphs
are connected. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_adj_same_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    {v w : ExternalInsertionVertex E S}
    (h : (layout.assembleDiagram S F).vertexGraph.Adj v w) :
    (layout.vertexEquiv S v).1 = (layout.vertexEquiv S w).1 := by
  obtain ⟨_, leg, hv, hw⟩ := h
  have hsource := congrArg Sigma.fst (layout.vertexEquiv_vertexOfLeg S leg)
  rw [hv] at hsource
  have htarget := congrArg Sigma.fst
    (layout.vertexEquiv_vertexOfLeg S
      ((layout.assembleDiagram S F).pairing.partner leg))
  rw [hw] at htarget
  exact hsource.trans ((PairingOn.sigmaCongrRight_transport_partner_fst
    (fun B => (F B).pairing) (layout.legEquiv S) leg).symm.trans htarget.symm)

/-- All vertices connected by a path in an independently assembled diagram
belong to the same prescribed external block. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_reachable_same_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    {v w : ExternalInsertionVertex E S}
    (h : (layout.assembleDiagram S F).vertexGraph.Reachable v w) :
    (layout.vertexEquiv S v).1 = (layout.vertexEquiv S w).1 := by
  simpa only [Relation.reflTransGen_eq_self] using
    (Relation.ReflTransGen.lift (p := Eq)
      (fun x : ExternalInsertionVertex E S => (layout.vertexEquiv S x).1)
      (fun _ _ hadj => layout.assembleDiagram_adj_same_block S F hadj))
      v w ((SimpleGraph.reachable_iff_reflTransGen _ _).mp h)

/-- Undo the flattened-leg equivalence at one local leg while
keeping its incident vertex. -/
theorem ExternalInsertionBlockLayout.vertexOfLeg_legEquiv_symm
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (B : layout.partition.parts)
    (leg : Fin (2 * (2 * (layout.interactionBlock S B).card +
      ((B : Finset (Fin (2 * E))).card / 2)))) :
    externalInsertionVertexOfLeg ((layout.legEquiv S).symm ⟨B, leg⟩) =
      (layout.vertexEquiv S).symm ⟨B, externalInsertionVertexOfLeg leg⟩ := by
  apply (layout.vertexEquiv S).injective
  rw [layout.vertexEquiv_vertexOfLeg]
  rw [(layout.legEquiv S).apply_symm_apply]
  rw [(layout.vertexEquiv S).apply_symm_apply]

/-- Every local block vertex graph maps into the assembled physical graph.
In particular, this map transports a local connected path into a physical
connected path; it preserves interaction vertices as well as sources. -/
noncomputable def ExternalInsertionBlockLayout.blockGraphHom
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (B : layout.partition.parts) :
    (F B).vertexGraph →g (layout.assembleDiagram S F).vertexGraph where
  toFun u := (layout.vertexEquiv S).symm ⟨B, u⟩
  map_rel' := by
    intro u v h
    obtain ⟨hne, leg, hu, hv⟩ := h
    refine ⟨?_, (layout.legEquiv S).symm ⟨B, leg⟩, ?_, ?_⟩
    · intro hEq
      apply hne
      have hSigma := (layout.vertexEquiv S).symm.injective hEq
      exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
    · rw [layout.vertexOfLeg_legEquiv_symm, hu]
    · rw [layout.assembleDiagram_partner,
        layout.vertexOfLeg_legEquiv_symm, hv]

/-- Between two vertices belonging to one prescribed external block,
the assembled physical graph has an edge exactly when the corresponding
local graph has that edge. In particular, an ambient edge cannot introduce
additional adjacency within a block beyond its local pairing. -/
theorem ExternalInsertionBlockLayout.blockGraphHom_adj_iff
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (B : layout.partition.parts)
    (u v : ExternalInsertionVertex
      ((B : Finset (Fin (2 * E))).card / 2) (layout.interactionBlock S B)) :
    (F B).vertexGraph.Adj u v ↔
      (layout.assembleDiagram S F).vertexGraph.Adj
        ((layout.vertexEquiv S).symm ⟨B, u⟩)
        ((layout.vertexEquiv S).symm ⟨B, v⟩) := by
  constructor
  · intro h
    exact (layout.blockGraphHom S F B).map_rel h
  · rintro ⟨hne, leg, hsrc, htar⟩
    obtain ⟨⟨C, p⟩, rfl⟩ := (layout.legEquiv S).symm.surjective leg
    have hSrc :
        (layout.vertexEquiv S).symm ⟨C, externalInsertionVertexOfLeg p⟩ =
          (layout.vertexEquiv S).symm ⟨B, u⟩ := by
      rw [← layout.vertexOfLeg_legEquiv_symm]
      exact hsrc
    have hSig := (layout.vertexEquiv S).symm.injective hSrc
    have hCB : C = B := congrArg Sigma.fst hSig
    subst C
    have hu : externalInsertionVertexOfLeg p = u :=
      eq_of_heq (Sigma.mk.inj_iff.mp hSig).2
    have hTar :
        (layout.vertexEquiv S).symm
            ⟨B, externalInsertionVertexOfLeg ((F B).pairing.partner p)⟩ =
          (layout.vertexEquiv S).symm ⟨B, v⟩ := by
      rw [← layout.vertexOfLeg_legEquiv_symm,
        ← layout.assembleDiagram_partner S F B p]
      exact htar
    have hv : externalInsertionVertexOfLeg ((F B).pairing.partner p) = v :=
      eq_of_heq (Sigma.mk.inj_iff.mp
        ((layout.vertexEquiv S).symm.injective hTar)).2
    refine ⟨?_, p, hu, hv⟩
    intro huv
    exact hne (congrArg
      (fun w => (layout.vertexEquiv S).symm ⟨B, w⟩) huv)

/-- For vertices within one prescribed external block, local
reachability is equivalent to physical reachability after assembly.
The reverse implication follows by lifting each physical edge of a
path back into the corresponding local pairing, using the exact
blockwise adjacency equivalence. -/
theorem ExternalInsertionBlockLayout.blockGraphHom_reachable_iff
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (B : layout.partition.parts)
    (u v : ExternalInsertionVertex
      ((B : Finset (Fin (2 * E))).card / 2) (layout.interactionBlock S B)) :
    (F B).vertexGraph.Reachable u v ↔
      (layout.assembleDiagram S F).vertexGraph.Reachable
        ((layout.vertexEquiv S).symm ⟨B, u⟩)
        ((layout.vertexEquiv S).symm ⟨B, v⟩) := by
  constructor
  · intro h
    exact h.map (layout.blockGraphHom S F B)
  · intro h
    refine SimpleGraph.reachable_of_closed_image
      (fun x => (layout.vertexEquiv S).symm ⟨B, x⟩) ?_ ?_ ?_ h
    · intro a b he
      exact eq_of_heq (Sigma.mk.inj_iff.mp ((layout.vertexEquiv S).symm.injective he)).2
    · intro a b ha
      exact (layout.blockGraphHom_adj_iff S F B a b).2 ha
    · intro a z ha
      obtain ⟨⟨C, w⟩, rfl⟩ := (layout.vertexEquiv S).symm.surjective z
      have hBC : B = C := by
        simpa only [Equiv.apply_symm_apply] using
          (layout.assembleDiagram_adj_same_block S F ha)
      subst C
      exact ⟨w, rfl⟩

/-- If all independently supplied local graphs are preconnected, then
global reachability is exactly agreement of the assigned external blocks.
The forward implication holds without any connectedness assumptions. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_reachable_iff_same_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (v w : ExternalInsertionVertex E S) :
    (layout.assembleDiagram S F).vertexGraph.Reachable v w ↔
      (layout.vertexEquiv S v).1 = (layout.vertexEquiv S w).1 := by
  constructor
  · exact layout.assembleDiagram_reachable_same_block S F
  · intro hblock
    obtain ⟨⟨B, u⟩, hv⟩ := (layout.vertexEquiv S).symm.surjective v
    obtain ⟨⟨C, w'⟩, hw⟩ := (layout.vertexEquiv S).symm.surjective w
    rw [← hv, ← hw] at hblock ⊢
    simp only [Equiv.apply_symm_apply] at hblock
    subst C
    exact ((hconnected B) u w').map (layout.blockGraphHom S F B)

/-- The block selected by the increasing source-slot equivalence is
precisely the part of the prescribed partition containing that source. -/
@[simp]
theorem ExternalInsertionBlockLayout.sourceEquiv_fst
    (layout : ExternalInsertionBlockLayout E N) (e : Fin (2 * E)) :
    ((layout.sourceEquiv e).1 : Finset (Fin (2 * E))) =
      layout.partition.part e := by
  rfl

/-- Independent assembly of preconnected local diagrams has exactly the
prescribed external connected-component partition. This is a statement
about actual assembled pairings, not a postulated partition of diagrams. -/
theorem ExternalInsertionBlockLayout.externalComponentPartition_assembleDiagram
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected) :
    externalComponentPartition (layout.assembleDiagram S F).vertexGraph =
      layout.partition := by
  classical
  have howner (e f : Fin (2 * E)) :
      (layout.sourceEquiv e).1 = (layout.sourceEquiv f).1 ↔
        f ∈ layout.partition.part e := by
    constructor
    · intro h
      have heq : layout.partition.part f = layout.partition.part e := by
        simpa only [layout.sourceEquiv_fst] using
          (congrArg Subtype.val h).symm
      exact (layout.partition.mem_part_iff_part_eq_part
        (Finset.mem_univ f) (Finset.mem_univ e)).2 heq
    · intro h
      have heq := (layout.partition.mem_part_iff_part_eq_part
        (Finset.mem_univ f) (Finset.mem_univ e)).1 h
      apply Subtype.ext
      simpa only [layout.sourceEquiv_fst] using heq.symm
  have hpart (e : Fin (2 * E)) :
      (externalComponentPartition (layout.assembleDiagram S F).vertexGraph).part e =
        layout.partition.part e := by
    ext f
    rw [mem_externalComponentPartition_part,
      layout.assembleDiagram_reachable_iff_same_block S F hconnected]
    simpa only [layout.vertexEquiv_external] using (howner e f)
  exact Finpartition.eq_of_part_eq_on _ _ (fun e _ => hpart e)

/-- The physical connected component's external sector is exactly
the prescribed source-partition block. Together with the full-vertex
component identity, this identifies the external sector of the assembled
component without changing the fermionic source order. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentExternalSector_external
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    Finset.toLeft ((layout.assembleDiagram S F).vertexGraph.componentBlock
        (Sum.inl e)) =
      ((layout.sourceEquiv e).1 : Finset (Fin (2 * E))) := by
  rw [← externalComponentPartition_part_eq_toLeft_componentBlock,
    layout.externalComponentPartition_assembleDiagram S F hconnected,
    layout.sourceEquiv_fst]

/-- The interaction sector of the actual physical component containing
an external insertion is exactly the set of ambient quartic vertices
assigned to that source block. This is the interaction-side companion
to `assembleDiagram_componentExternalSector_external`; both sector
identities hold at the original vertex indices. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentInteractionSector_external
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    interactionSector ((layout.assembleDiagram S F).vertexGraph.componentBlock
        (Sum.inl e)) =
      layout.interactionBlock S (layout.sourceEquiv e).1 := by
  classical
  let d := layout.assembleDiagram S F
  ext v
  rw [mem_interactionSector, ExternalInsertionBlockLayout.interactionBlock, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hmem⟩
    exact ⟨hv, (layout.assembleDiagram_reachable_iff_same_block S F hconnected
      (Sum.inr ⟨v, hv⟩) (Sum.inl e)).mp
        ((d.vertexGraph.mem_componentBlock (Sum.inl e) (Sum.inr ⟨v, hv⟩)).mp hmem)⟩
  · rintro ⟨hv, howner⟩
    exact ⟨hv, (d.vertexGraph.mem_componentBlock (Sum.inl e) (Sum.inr ⟨v, hv⟩)).mpr
      ((layout.assembleDiagram_reachable_iff_same_block S F hconnected
        (Sum.inr ⟨v, hv⟩) (Sum.inl e)).mpr howner)⟩

/-- The legs of the *actual physical* connected component containing
an external insertion are exactly the legs assigned to its independent
source block by the global flattened-leg equivalence. This identifies
the domain of physical pairing restriction with the block's entire leg
fiber, including interaction legs and zero-interaction blocks. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_legInComponent_iff_legEquiv_fst
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E))
    (leg : Fin (2 * (2 * S.card + E))) :
    (layout.assembleDiagram S F).legInComponent
        ((layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e)) leg ↔
      (layout.legEquiv S leg).1 = (layout.sourceEquiv e).1 := by
  classical
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  change d.legInComponent C.1 leg ↔ _
  rw [d.legInComponent_iff_vertex_mem C.2 leg]
  change externalInsertionVertexOfLeg leg ∈ d.vertexGraph.componentBlock (Sum.inl e) ↔ _
  rw [d.vertexGraph.mem_componentBlock]
  rw [layout.assembleDiagram_reachable_iff_same_block S F hconnected]
  rw [layout.vertexEquiv_vertexOfLeg S leg, layout.vertexEquiv_external]

/-- Canonical identification of the legs in an *actual* connected graph
component with the flattened legs of its independently assigned Wick
block. Unlike a cardinality argument, this equivalence retains every
individual source and interaction leg of the physical pairing. -/
noncomputable def ExternalInsertionBlockLayout.physicalComponentLegEquiv
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    {leg : Fin (2 * (2 * S.card + E)) //
      (layout.assembleDiagram S F).legInComponent
        ((layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e)) leg} ≃
      Fin (2 * (2 * (layout.interactionBlock S (layout.sourceEquiv e).1).card +
        ((layout.sourceEquiv e).1.1.card / 2))) :=
  ((layout.legEquiv S).subtypeEquiv
    (layout.assembleDiagram_legInComponent_iff_legEquiv_fst S F hconnected e)).trans
    (Equiv.sigmaSubtype (layout.sourceEquiv e).1)

/-- A local leg embedded by the physical-component equivalence is
exactly that same leg embedded by independent block assembly. -/
theorem ExternalInsertionBlockLayout.physicalComponentLegEquiv_symm_val
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E))
    (i : Fin (2 * (2 * (layout.interactionBlock S (layout.sourceEquiv e).1).card +
      ((layout.sourceEquiv e).1.1.card / 2)))) :
    ((layout.physicalComponentLegEquiv S F hconnected e).symm i).1 =
      (layout.legEquiv S).symm ⟨(layout.sourceEquiv e).1, i⟩ := by
  rfl

/-- The canonical connected-component pairing agrees with the original
independent Wick block pairing after the *explicit* change from canonical
physical component-leg coordinates to assigned block-leg coordinates.
Unlike blockwise assembly alone, the left-hand side starts with the
actual graph component restricted from the assembled physical diagram.
The change of coordinates accounts for the distinct dependent local
interaction-slot and external-pair indices. -/
theorem ExternalInsertionBlockLayout.physicalComponentCanonicalPairing_eq_local
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    (let d := layout.assembleDiagram S F
     let C : d.vertexGraph.componentPartition.parts :=
       ⟨d.vertexGraph.componentBlock (Sum.inl e),
         d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
     (d.restrictComponent C).pairing.transport
       ((d.componentBlockLegEquiv C).symm.trans
         (layout.physicalComponentLegEquiv S F hconnected e)).symm) =
      (F (layout.sourceEquiv e).1).pairing := by
  classical
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  let T := layout.physicalComponentLegEquiv S F hconnected e
  let P := d.pairing.restrictAlongEquiv (d.legInComponent C.1)
    (d.legInComponent_partner_iff C.1) T
  change (d.restrictComponent C).pairing.transport
      ((d.componentBlockLegEquiv C).symm.trans T).symm =
      (F B).pairing
  have htransport : (d.restrictComponent C).pairing.transport
      ((d.componentBlockLegEquiv C).symm.trans T).symm = P := by
    simpa [ExternalInsertionDiagram.restrictComponent, P] using
      (d.pairing.restrictAlongEquiv_change_coordinates
        (d.legInComponent C.1) (d.legInComponent_partner_iff C.1)
        (d.componentBlockLegEquiv C) T)
  rw [htransport]
  apply PairingOn.ext
  apply Equiv.ext
  intro i
  have hpair : (T.symm (P.partner i)).1 =
      d.pairing.partner (T.symm i).1 :=
    d.pairing.restrictAlongEquiv_partner_symm_val
      (d.legInComponent C.1) (d.legInComponent_partner_iff C.1) T i
  have hpair' :
      (layout.legEquiv S).symm ⟨B, P.partner i⟩ =
        d.pairing.partner ((layout.legEquiv S).symm ⟨B, i⟩) := by
    simpa only [T, layout.physicalComponentLegEquiv_symm_val] using hpair
  rw [layout.assembleDiagram_partner S F B i] at hpair'
  have hsigma := (layout.legEquiv S).symm.injective hpair'
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

/-- The local external-pair parameter of an actual assembled graph component
is the half-cardinality of its assigned source-partition block. This closes
the dependent external-size index needed to identify physical component
restriction with the independently supplied labelled Wick block. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentExternalPairCount_external
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    (layout.assembleDiagram S F).externalPairCount
      ⟨(layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e),
        (layout.assembleDiagram S F).vertexGraph.componentBlock_mem_componentPartition
          (Sum.inl e)⟩ =
      ((layout.sourceEquiv e).1.1.card / 2) := by
  change (Finset.toLeft
    ((layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e))).card / 2 =
      ((layout.sourceEquiv e).1.1.card / 2)
  rw [layout.assembleDiagram_componentExternalSector_external S F hconnected e]

/-- The particular physical component-to-independent-block leg equivalence
is just the equality cast of *ordered flattened-leg indices*.  There is
no residual permutation: strict monotonicity and the
uniqueness of increasing equivalences between finite initial segments
force the full coordinate identification, even for zero interaction
vertices.  This is the cast-level bridge for comparing timed fields
without assuming symmetry under swapping fermionic endpoints. -/
theorem ExternalInsertionBlockLayout.physicalComponentCanonicalLegEquiv_eq_finCongr
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    let d := layout.assembleDiagram S F
    let C : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inl e),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
    let B := (layout.sourceEquiv e).1
    let hlegs : 2 * (2 * (interactionSector
        (C : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount C) =
      2 * (2 * (layout.interactionBlock S B).card + B.1.card / 2) := by
      rw [layout.assembleDiagram_componentInteractionSector_external
        S F hconnected e, layout.assembleDiagram_componentExternalPairCount_external
          S F hconnected e]
    (d.componentBlockLegEquiv C).symm.trans
      (layout.physicalComponentLegEquiv S F hconnected e) = finCongr hlegs := by
  classical
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  let B := (layout.sourceEquiv e).1
  let hlegs : 2 * (2 * (interactionSector
      (C : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount C) =
      2 * (2 * (layout.interactionBlock S B).card + B.1.card / 2) := by
    rw [layout.assembleDiagram_componentInteractionSector_external
      S F hconnected e, layout.assembleDiagram_componentExternalPairCount_external
        S F hconnected e]
  let c := (d.componentBlockLegEquiv C).symm.trans
    (layout.physicalComponentLegEquiv S F hconnected e)
  change c = finCongr hlegs
  have hc : StrictMono c := by
    have hbridge (p : Fin (2 * (2 * (interactionSector
        (C : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount C))) :
        (layout.legEquiv S).symm ⟨B, c p⟩ =
          d.componentDiagramLeg C p := by
      calc
        (layout.legEquiv S).symm ⟨B, c p⟩ =
            ((layout.physicalComponentLegEquiv S F hconnected e).symm (c p)).1 :=
          (layout.physicalComponentLegEquiv_symm_val S F hconnected e (c p)).symm
        _ = ((d.componentBlockLegEquiv C).symm p).1 := by
          change ((layout.physicalComponentLegEquiv S F hconnected e).symm
            ((layout.physicalComponentLegEquiv S F hconnected e)
              ((d.componentBlockLegEquiv C).symm p))).1 = _
          rw [Equiv.symm_apply_apply]
        _ = d.componentDiagramLeg C p := rfl
    intro i j hij
    have hglobal : d.componentDiagramLeg C i < d.componentDiagramLeg C j := by
      simpa only [d.componentLegShuffle_slotEquiv_apply] using
        (d.componentLegShuffle.strictMono C) hij
    have hlocal := layout.blockLegEmbedding_strictMono S B
    apply hlocal.lt_iff_lt.mp
    rw [hbridge i, hbridge j]
    exact hglobal
  let iso : Fin (2 * (2 * (interactionSector
      (C : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount C)) ≃o
      Fin (2 * (2 * (layout.interactionBlock S B).card + B.1.card / 2)) :=
    { toEquiv := c
      map_rel_iff' := by
        intro a b
        exact hc.le_iff_le }
  apply Equiv.ext
  intro p
  apply Fin.ext
  change (c p).val = p.val
  exact Fin.coe_orderIso_apply iso p

/-- Equal finite supports allow pointwise equality of dependent subtype
functions to be promoted to heterogeneous equality of the functions. -/
private theorem heq_subtypeFunctions_of_finset_eq
    {α β : Type*} {S T : Finset α}
    (f : ↥S → β) (g : ↥T → β) (hST : S = T)
    (h : ∀ v : ↥S, f v = g ⟨v.1, hST ▸ v.2⟩) :
    HEq f g := by
  cases hST
  exact heq_of_eq (funext h)

/-- The actual physical connected-component restriction and the
independently supplied block have *heterogeneously equal vertex-label
families*. Their indexing sets are equal because the assembled graph has
precisely the prescribed interaction component, not merely the same
cardinality. This is the dependent-type form needed before standardizing
the local interaction slots. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_restrictComponent_vertexLabel_heq
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    HEq (F (layout.sourceEquiv e).1).vertexLabel
      ((layout.assembleDiagram S F).restrictComponent
        ⟨(layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e),
          (layout.assembleDiagram S F).vertexGraph.componentBlock_mem_componentPartition
            (Sum.inl e)⟩).vertexLabel := by
  classical
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  change HEq (F B).vertexLabel (d.restrictComponent C).vertexLabel
  refine heq_subtypeFunctions_of_finset_eq
    (F B).vertexLabel (d.restrictComponent C).vertexLabel
    (layout.assembleDiagram_componentInteractionSector_external S F hconnected e).symm ?_
  intro v
  have hidx :
      ((layout.interactionEquiv S).symm ⟨B, v⟩ : ↥S) =
        ⟨v.1, (Finset.mem_filter.mp v.2).1⟩ := by
    apply Subtype.ext
    rfl
  have hlabel := layout.assembleDiagram_vertexLabel S F B v
  rw [hidx] at hlabel
  exact hlabel.symm

/-- Connected local blocks also ensure that no internal-only vacuum
component survives the assembly. Each prescribed partition part is
nonempty and therefore supplies an external vertex reachable from all
its assigned interaction vertices. -/
theorem ExternalInsertionBlockLayout.hasNoVacuumComponent_assembleDiagram
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected) :
    HasNoVacuumComponent (layout.assembleDiagram S F).vertexGraph := by
  intro v
  let B : layout.partition.parts := (layout.interactionEquiv S v).1
  have hnonempty : (B : Finset (Fin (2 * E))).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (layout.partition.ne_bot B.2)
  obtain ⟨e, he⟩ := hnonempty
  refine ⟨e, ?_⟩
  apply (layout.assembleDiagram_reachable_iff_same_block S F hconnected
    (Sum.inl e) (Sum.inr v)).2
  have hsource : (layout.sourceEquiv e).1 = B := by
    apply Subtype.ext
    simpa only [layout.sourceEquiv_fst] using
      (layout.partition.part_eq_of_mem B.2 he)
  simpa only [layout.vertexEquiv_external, layout.vertexEquiv_interaction] using
    hsource

/-- Independent block assembly is **injective on the complete labelled
diagram data**: all local external labels, interaction labels and pairing
partners can be recovered from the assembled diagram.

This is the essential inverse-information statement for arbitrary external
partitions, separate from the remaining proof that connected local diagrams
produce exactly the prescribed graph component partition. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_injective
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    Function.Injective (layout.assembleDiagram (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel) S) := by
  intro F G h
  funext B
  apply ExternalInsertionDiagram.ext
  · funext e
    have he := congrArg (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.externalLabel (layout.sourceEquiv.symm ⟨B, e⟩)) h
    simpa only [layout.assembleDiagram_externalLabel] using he
  · funext v
    have hv := congrArg (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.vertexLabel ((layout.interactionEquiv S).symm ⟨B, v⟩)) h
    simpa only [layout.assembleDiagram_vertexLabel] using hv
  · apply Combinatorics.PairingOn.ext
    apply Equiv.ext
    intro p
    have hp := congrArg (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.pairing.partner ((layout.legEquiv S).symm ⟨B, p⟩)) h
    simp only [layout.assembleDiagram_partner] at hp
    have hpair := (layout.legEquiv S).symm.injective hp
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2



/-- A pairing whose partners stay in their prescribed external blocks
also preserves the dependent sigma index after transport by the concrete
flattened-leg equivalence. -/
private theorem ExternalInsertionBlockLayout.pairingTransport_preserves_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hblock : ∀ leg,
      (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) :
    ∀ x, ((d.pairing.transport (layout.legEquiv S).symm).partner x).1 = x.1 := by
  intro x
  have hx := hblock ((layout.legEquiv S).symm x)
  simpa only [PairingOn.transport_partner, Equiv.symm_symm,
    Equiv.apply_symm_apply] using hx

/-- Extract a labelled local diagram from a physical pairing respecting a
prescribed independent-block layout. Local external slots and interaction
vertices retain their original ambient identities and order; the local
pairing is obtained by restricting the transported ambient involution. -/
noncomputable def ExternalInsertionBlockLayout.restrictBlock
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hblock : ∀ leg,
      (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1)
    (B : layout.partition.parts) :
    ExternalInsertionDiagram ExternalLabel InternalLabel
      ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) where
  externalLabel e := d.externalLabel (layout.sourceEquiv.symm ⟨B, e⟩)
  vertexLabel v := d.vertexLabel ((layout.interactionEquiv S).symm ⟨B, v⟩)
  pairing := (d.pairing.transport (layout.legEquiv S).symm).sigmaFiberPairing
    (layout.pairingTransport_preserves_block S d hblock) B

/-- Reassembly of all restricted labelled blocks recovers exactly the
original physical diagram, including every label and pairing partner. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_restrictBlock
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hblock : ∀ leg,
      (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) :
    layout.assembleDiagram S (layout.restrictBlock S d hblock) = d := by
  apply ExternalInsertionDiagram.ext
  · funext e
    change d.externalLabel (layout.sourceEquiv.symm (layout.sourceEquiv e)) =
      d.externalLabel e
    rw [Equiv.symm_apply_apply]
  · funext v
    change d.vertexLabel ((layout.interactionEquiv S).symm
      (layout.interactionEquiv S v)) = d.vertexLabel v
    rw [Equiv.symm_apply_apply]
  · change
      (PairingOn.sigmaCongrRight (fun B =>
        (d.pairing.transport (layout.legEquiv S).symm).sigmaFiberPairing
          (layout.pairingTransport_preserves_block S d hblock) B)).transport
        (layout.legEquiv S) = d.pairing
    rw [PairingOn.sigmaCongrRight_sigmaFiberPairing,
      PairingOn.transport_transport_symm]

/-- Restriction is also a left inverse of independent assembly, without
a connectedness hypothesis: the assembled pairing respects every assigned
block, and injectivity of assembly recovers all local diagram data. -/
theorem ExternalInsertionBlockLayout.restrictBlock_assembleDiagram
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) :
    (fun B => layout.restrictBlock S (layout.assembleDiagram S F)
      (PairingOn.sigmaCongrRight_transport_partner_fst (fun B => (F B).pairing)
        (layout.legEquiv S)) B) = F := by
  apply layout.assembleDiagram_injective S
  exact layout.assembleDiagram_restrictBlock S
    (layout.assembleDiagram S F)
    (PairingOn.sigmaCongrRight_transport_partner_fst (fun B => (F B).pairing)
      (layout.legEquiv S))


/-- The assembled diagram has prescribed external field labels exactly
when every local block carries the induced increasing-order restriction
of those labels. No relative ordering of the numerical times is used. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_iff
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (labels : Fin (2 * E) → ExternalLabel) :
    (layout.assembleDiagram S F).externalLabel = labels ↔
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩) := by
  constructor
  · intro h B
    funext i
    rw [← layout.assembleDiagram_externalLabel S F B i]
    exact congrFun h (layout.sourceEquiv.symm ⟨B, i⟩)
  · intro h
    funext e
    obtain ⟨⟨B, i⟩, rfl⟩ := layout.sourceEquiv.symm.surjective e
    rw [layout.assembleDiagram_externalLabel]
    exact congrFun (h B) i

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
      vacuumFreeComponentsEquivExternalBlocks d.vertexGraph hVac
        ⟨d.vertexGraph.componentBlock (Sum.inr (⟨v, hv⟩ : ↥S)),
          d.vertexGraph.componentBlock_mem_componentPartition
            (Sum.inr (⟨v, hv⟩ : ↥S))⟩
    else
      ⟨(externalComponentPartition d.vertexGraph).part anchor,
        (externalComponentPartition d.vertexGraph).part_mem.2
          (Finset.mem_univ anchor)⟩

/-- On active interaction vertices the layout assignment is the unique
actual connected component, identified with its external block. -/
theorem ExternalInsertionDiagram.externalBlockLayout_interactionOwner
    {ExternalLabel InternalLabel : Type*} {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (anchor : Fin (2 * E)) (v : ↥S) :
    (d.externalBlockLayout hVac anchor).interactionOwner v.1 =
      vacuumFreeComponentsEquivExternalBlocks d.vertexGraph hVac
        ⟨d.vertexGraph.componentBlock (Sum.inr v),
          d.vertexGraph.componentBlock_mem_componentPartition (Sum.inr v)⟩ := by
  simp [ExternalInsertionDiagram.externalBlockLayout, v.2]

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
        (((vacuumFreeComponentsEquivExternalBlocks d.vertexGraph hVac).symm P).1 :
          Finset (ExternalInsertionVertex E S)) := by
  classical
  let equiv := vacuumFreeComponentsEquivExternalBlocks d.vertexGraph hVac
  have howner (V : ↥S) :
      (d.externalBlockLayout hVac anchor).interactionOwner V.1 = P ↔
        (Sum.inr V : ExternalInsertionVertex E S) ∈ (equiv.symm P).1 := by
    let C : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inr V),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inr V)⟩
    constructor
    · intro h
      rw [d.externalBlockLayout_interactionOwner hVac anchor V] at h
      have heq : equiv C = P := h
      have hC : C = equiv.symm P :=
        equiv.injective (heq.trans (equiv.apply_symm_apply P).symm)
      have hmem : (Sum.inr V : ExternalInsertionVertex E S) ∈ C.1 :=
        d.vertexGraph.self_mem_componentBlock (Sum.inr V)
      simpa only [hC] using hmem
    · intro h
      have hC : C = equiv.symm P := by
        apply Subtype.ext
        exact (d.vertexGraph.componentBlock_eq_iff_mem
          (equiv.symm P).2 (Sum.inr V)).2 h
      rw [d.externalBlockLayout_interactionOwner hVac anchor V]
      change equiv C = P
      rw [hC, Equiv.apply_symm_apply]
  ext v
  constructor
  · intro hv
    have hfilter : v ∈ S ∧
        (d.externalBlockLayout hVac anchor).interactionOwner v = P := by
      simpa only [ExternalInsertionBlockLayout.interactionBlock,
        Finset.mem_filter] using hv
    exact (mem_interactionSector _ v).2
      ⟨hfilter.1, (howner ⟨v, hfilter.1⟩).1 hfilter.2⟩
  · intro hv
    obtain ⟨hvS, hmem⟩ := (mem_interactionSector _ v).1 hv
    simpa only [ExternalInsertionBlockLayout.interactionBlock,
      Finset.mem_filter] using (show v ∈ S ∧
      (d.externalBlockLayout hVac anchor).interactionOwner v = P from
        ⟨hvS, (howner ⟨v, hvS⟩).2 hmem⟩)


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
      exact externalComponentPartition_part_eq_toLeft_componentBlock d.vertexGraph e
  | inr w =>
      change ((d.externalBlockLayout hVac anchor).interactionOwner w.1).1 =
        (d.vertexGraph.componentBlock (Sum.inr w)).toLeft
      rw [d.externalBlockLayout_interactionOwner hVac anchor w]
      exact vacuumFreeComponentsEquivExternalBlocks_apply d.vertexGraph hVac _

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
  let e := vacuumFreeComponentsEquivExternalBlocks d.vertexGraph hVac
  let C (x : ExternalInsertionVertex E S) : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock x,
      d.vertexGraph.componentBlock_mem_componentPartition x⟩
  have howner (x : ExternalInsertionVertex E S) :
      ((d.externalBlockLayout hVac anchor).vertexEquiv S x).1 = e (C x) := by
    apply Subtype.ext
    exact (d.externalBlockLayout_vertexPart hVac anchor x).trans
      (vacuumFreeComponentsEquivExternalBlocks_apply d.vertexGraph hVac (C x)).symm
  rw [howner v, howner w]
  constructor
  · intro h
    exact congrArg e (Subtype.ext (d.vertexGraph.componentBlock_eq_of_reachable h))
  · intro h
    exact (d.vertexGraph.componentBlock_eq_iff_reachable v w).mp
      (congrArg Subtype.val (e.injective h))

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
  calc
    (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.vertexEquiv S (externalInsertionVertexOfLeg (d.pairing.partner leg))).1 :=
      (congrArg Sigma.fst (layout.vertexEquiv_vertexOfLeg S (d.pairing.partner leg))).symm
    _ = (layout.vertexEquiv S (externalInsertionVertexOfLeg leg)).1 :=
      (d.reachable_iff_externalBlockLayout_same_block hVac anchor _ _).mp
        (d.pairing.vertexGraph_reachable_partner (externalInsertionVertexOfLeg (E := E)) leg)
    _ = _ := congrArg Sigma.fst (layout.vertexEquiv_vertexOfLeg S leg)

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
  let d := layout.assembleDiagram S F
  let hVac := layout.hasNoVacuumComponent_assembleDiagram S F hconnected
  let physical := d.externalBlockLayout hVac anchor
  obtain ⟨e, hReach⟩ := hVac v
  have hsource : (layout.sourceEquiv e).1 = layout.interactionOwner v.1 := by
    have heq : (layout.sourceEquiv e).1 = (layout.interactionEquiv S v).1 := by
      simpa only [layout.vertexEquiv_external, layout.vertexEquiv_interaction] using
        (layout.assembleDiagram_reachable_iff_same_block S F hconnected
          (Sum.inl e) (Sum.inr v)).mp hReach
    exact heq.trans (by rfl)
  have hphysical : (physical.sourceEquiv e).1 = physical.interactionOwner v.1 := by
    have heq : (physical.vertexEquiv S (Sum.inl e)).1 =
        (physical.vertexEquiv S (Sum.inr v)).1 :=
      (d.reachable_iff_externalBlockLayout_same_block hVac anchor
        (Sum.inl e) (Sum.inr v)).mp hReach
    rw [physical.vertexEquiv_external, physical.vertexEquiv_interaction] at heq
    exact heq.trans (by rfl)
  calc
    _ = physical.partition.part e :=
      (congrArg Subtype.val hphysical).symm.trans (physical.sourceEquiv_fst e)
    _ = layout.partition.part e := by
      change (externalComponentPartition d.vertexGraph).part e = _
      rw [layout.externalComponentPartition_assembleDiagram S F hconnected]
    _ = _ := (layout.sourceEquiv_fst e).symm.trans (congrArg Subtype.val hsource)


end Common
end SecondQuantization
