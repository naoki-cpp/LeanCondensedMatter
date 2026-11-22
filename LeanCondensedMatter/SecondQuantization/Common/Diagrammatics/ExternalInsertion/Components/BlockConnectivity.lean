import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockLayout

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
  exact hsource.trans ((layout.assembleDiagram_partner_block S F leg).symm.trans
    htarget.symm)

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

/-- In particular, different prescribed external partition blocks never
become connected through the assembled pairing. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_external_reachable_same_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    {e f : Fin (2 * E)}
    (h : (layout.assembleDiagram S F).vertexGraph.Reachable (Sum.inl e) (Sum.inl f)) :
    (layout.sourceEquiv e).1 = (layout.sourceEquiv f).1 := by
  simpa only [layout.vertexEquiv_external] using
    (layout.assembleDiagram_reachable_same_block S F h)

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
    have hPath :
        Relation.ReflTransGen (layout.assembleDiagram S F).vertexGraph.Adj
          ((layout.vertexEquiv S).symm ⟨B, u⟩)
          ((layout.vertexEquiv S).symm ⟨B, v⟩) :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).mp h
    have hLift : ∀ {z : ExternalInsertionVertex E S},
        Relation.ReflTransGen (layout.assembleDiagram S F).vertexGraph.Adj
            ((layout.vertexEquiv S).symm ⟨B, u⟩) z →
          ∃ w, z = (layout.vertexEquiv S).symm ⟨B, w⟩ ∧
            (F B).vertexGraph.Reachable u w := by
      intro z hz
      induction hz with
      | refl =>
          exact ⟨u, rfl, SimpleGraph.Reachable.refl u⟩
      | @tail a c _ hadj ih =>
          obtain ⟨w, rfl, hw⟩ := ih
          have hsame : B = (layout.vertexEquiv S c).1 := by
            simpa only [Equiv.apply_symm_apply] using
              (layout.assembleDiagram_adj_same_block S F hadj)
          cases hc : layout.vertexEquiv S c with
          | mk C w' =>
              have hBC : B = C := by
                simpa only [hc] using hsame
              subst C
              have hval : c = (layout.vertexEquiv S).symm ⟨B, w'⟩ := by
                calc
                  c = (layout.vertexEquiv S).symm (layout.vertexEquiv S c) :=
                    ((layout.vertexEquiv S).symm_apply_apply c).symm
                  _ = _ := by rw [hc]
              have hEdge : (layout.assembleDiagram S F).vertexGraph.Adj
                  ((layout.vertexEquiv S).symm ⟨B, w⟩)
                  ((layout.vertexEquiv S).symm ⟨B, w'⟩) := by
                simpa only [hval] using hadj
              have hLocal := (layout.blockGraphHom_adj_iff S F B w w').2 hEdge
              exact ⟨w', hval, hw.trans (SimpleGraph.Adj.reachable hLocal)⟩
    obtain ⟨w, heq, hw⟩ := hLift hPath
    have hSig := (layout.vertexEquiv S).symm.injective heq.symm
    have hwv : w = v := eq_of_heq (Sigma.mk.inj_iff.mp hSig).2
    simpa only [hwv] using hw

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

/-- The actual physical connected component containing an external
insertion is *exactly* the image of its prescribed block's local
vertices under the assembly vertex equivalence. This includes every
quartic vertex, not only the external legs, and does not refer to a
relabelled diagram or to an assumed component decomposition. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentBlock_external
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    (layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e) =
      (Finset.univ : Finset
        (ExternalInsertionVertex ((layout.sourceEquiv e).1.1.card / 2)
          (layout.interactionBlock S (layout.sourceEquiv e).1))).image
        (fun v => (layout.vertexEquiv S).symm ⟨(layout.sourceEquiv e).1, v⟩) := by
  classical
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  ext v
  rw [d.vertexGraph.mem_componentBlock]
  rw [layout.assembleDiagram_reachable_iff_same_block S F hconnected]
  simp only [layout.vertexEquiv_external, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases hq : layout.vertexEquiv S v with ⟨C, w⟩
    have hCB : C = B := by
      simpa only [hq] using h
    subst C
    refine ⟨w, ?_⟩
    calc
      (layout.vertexEquiv S).symm ⟨B, w⟩ =
          (layout.vertexEquiv S).symm (layout.vertexEquiv S v) :=
        congrArg (layout.vertexEquiv S).symm hq.symm
      _ = v := (layout.vertexEquiv S).symm_apply_apply v
  · rintro ⟨w, hw⟩
    subst v
    simpa only [Equiv.apply_symm_apply]

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
  apply Finpartition.ext
  apply Finset.Subset.antisymm
  · intro B hB
    obtain ⟨e, -, he⟩ :=
      (externalComponentPartition (layout.assembleDiagram S F).vertexGraph).part_surjOn hB
    rw [← he, hpart e]
    exact layout.partition.part_mem.2 (Finset.mem_univ e)
  · intro B hB
    obtain ⟨e, -, he⟩ := layout.partition.part_surjOn hB
    rw [← he, ← hpart e]
    exact (externalComponentPartition (layout.assembleDiagram S F).vertexGraph).part_mem.2
      (Finset.mem_univ e)

/-- The physical connected component's external sector is exactly
the prescribed source-partition block. Together with the full-vertex
component identity, this identifies both sectors of the assembled
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
  let d := layout.assembleDiagram S F
  calc
    (d.vertexGraph.componentBlock (Sum.inl e)).toLeft =
        (externalComponentPartition d.vertexGraph).part e :=
      (d.externalComponentPartition_part_eq_toLeft_componentBlock e).symm
    _ = layout.partition.part e :=
      congrArg (fun π : Finpartition (Finset.univ : Finset (Fin (2 * E))) =>
        π.part e) (layout.externalComponentPartition_assembleDiagram S F hconnected)
    _ = ((layout.sourceEquiv e).1 : Finset (Fin (2 * E))) :=
      (layout.sourceEquiv_fst e).symm

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
  let B := (layout.sourceEquiv e).1
  ext v
  constructor
  · intro hv
    have hvS : v ∈ S := interactionSector_subset _ hv
    let V : ↥S := ⟨v, hvS⟩
    have hmem : (Sum.inr V : ExternalInsertionVertex E S) ∈
        d.vertexGraph.componentBlock (Sum.inl e) :=
      (mem_interactionSector_subtype _ V).1 hv
    have hreach : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr V) := by
      have hr := (d.vertexGraph.mem_componentBlock (Sum.inl e) (Sum.inr V)).mp hmem
      exact hr.symm
    have hblocks :=
      (layout.assembleDiagram_reachable_iff_same_block S F hconnected
        (Sum.inl e) (Sum.inr V)).1 hreach
    have howner : layout.interactionOwner v = B := by
      change B = layout.interactionOwner v at hblocks
      exact hblocks.symm
    change v ∈ S.filter (fun x => layout.interactionOwner x = B)
    exact Finset.mem_filter.mpr ⟨hvS, howner⟩
  · intro hv
    have hfilter : v ∈ S ∧ layout.interactionOwner v = B := by
      simpa only [ExternalInsertionBlockLayout.interactionBlock,
        Finset.mem_filter] using hv
    let V : ↥S := ⟨v, hfilter.1⟩
    have hblocks :
        (layout.vertexEquiv S (Sum.inl e)).1 =
          (layout.vertexEquiv S (Sum.inr V)).1 := by
      change B = layout.interactionOwner v
      exact hfilter.2.symm
    have hreach :=
      (layout.assembleDiagram_reachable_iff_same_block S F hconnected
        (Sum.inl e) (Sum.inr V)).2 hblocks
    have hmem : (Sum.inr V : ExternalInsertionVertex E S) ∈
        d.vertexGraph.componentBlock (Sum.inl e) := by
      rw [d.vertexGraph.mem_componentBlock]
      exact hreach.symm
    exact (mem_interactionSector_subtype _ V).2 hmem

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

end Common
end SecondQuantization
