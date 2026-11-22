import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockConnectivity

set_option linter.style.header false

/-!
# Physical connected components of assembled external blocks

Canonical leg identification, physical-component Wick pairings, label preservation,
and the relation between local data and actual graph-component restrictions.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

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
    (Combinatorics.sigmaFiberEquiv (layout.sourceEquiv e).1)

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

/-- Being an actual physical graph component is invariant under the
assembled perfect pairing; this justifies physical partner restriction. -/
private theorem ExternalInsertionBlockLayout.physicalComponentLeg_partner_iff
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (e : Fin (2 * E))
    (leg : Fin (2 * (2 * S.card + E))) :
    (layout.assembleDiagram S F).legInComponent
      ((layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e)) leg ↔
    (layout.assembleDiagram S F).legInComponent
      ((layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e))
        ((layout.assembleDiagram S F).pairing.partner leg) := by
  unfold ExternalInsertionDiagram.legInComponent
  change
    ((layout.assembleDiagram S F).pairing.vertexGraph
      (externalInsertionVertexOfLeg (E := E))).componentBlock
        (externalInsertionVertexOfLeg leg) =
      (layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e) ↔
    ((layout.assembleDiagram S F).pairing.vertexGraph
      (externalInsertionVertexOfLeg (E := E))).componentBlock
        (externalInsertionVertexOfLeg ((layout.assembleDiagram S F).pairing.partner leg)) =
      (layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e)
  rw [(layout.assembleDiagram S F).pairing.vertexGraph_componentBlock_partner
    (externalInsertionVertexOfLeg (E := E)) leg]

/-- The pairing obtained by restricting the actual physical component to
its legs, reindexed through their independent block-fiber equivalence. -/
noncomputable def ExternalInsertionBlockLayout.physicalComponentPairing
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    PairingOn (Fin (2 * (2 * (layout.interactionBlock S (layout.sourceEquiv e).1).card +
      ((layout.sourceEquiv e).1.1.card / 2)))) :=
  (layout.assembleDiagram S F).pairing.restrictAlongEquiv
    ((layout.assembleDiagram S F).legInComponent
      ((layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e)))
    (layout.physicalComponentLeg_partner_iff S F e)
    (layout.physicalComponentLegEquiv S F hconnected e)

/-- The *physical component-restricted* Wick pairing, not merely the
global assembled pairing, equals the independently supplied local
perfect pairing on each leg. No local pairing data are lost or changed
by building and then restricting the actual connected graph. -/
theorem ExternalInsertionBlockLayout.physicalComponentPairing_eq_local
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    layout.physicalComponentPairing S F hconnected e =
      (F (layout.sourceEquiv e).1).pairing := by
  classical
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  let P := layout.physicalComponentPairing S F hconnected e
  let T := layout.physicalComponentLegEquiv S F hconnected e
  apply PairingOn.ext
  apply Equiv.ext
  intro i
  have hpair : (T.symm (P.partner i)).1 =
      d.pairing.partner (T.symm i).1 := by
    exact d.pairing.restrictAlongEquiv_partner_symm_val
      (d.legInComponent (d.vertexGraph.componentBlock (Sum.inl e)))
      (layout.physicalComponentLeg_partner_iff S F e) T i
  have hpair' :
      (layout.legEquiv S).symm ⟨B, P.partner i⟩ =
        d.pairing.partner ((layout.legEquiv S).symm ⟨B, i⟩) := by
    simpa only [T, layout.physicalComponentLegEquiv_symm_val] using hpair
  rw [layout.assembleDiagram_partner S F B i] at hpair'
  have hsigma := (layout.legEquiv S).symm.injective hpair'
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

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
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  change (d.restrictComponent C).pairing.transport
      ((d.componentBlockLegEquiv C).symm.trans
        (layout.physicalComponentLegEquiv S F hconnected e)).symm =
      (F (layout.sourceEquiv e).1).pairing
  calc
    (d.restrictComponent C).pairing.transport
        ((d.componentBlockLegEquiv C).symm.trans
          (layout.physicalComponentLegEquiv S F hconnected e)).symm =
      layout.physicalComponentPairing S F hconnected e := by
        simpa [ExternalInsertionDiagram.restrictComponent,
          ExternalInsertionBlockLayout.physicalComponentPairing] using
          (d.pairing.restrictAlongEquiv_change_coordinates
            (d.legInComponent C.1)
            (layout.physicalComponentLeg_partner_iff S F e)
            (d.componentBlockLegEquiv C)
            (layout.physicalComponentLegEquiv S F hconnected e))
    _ = (F (layout.sourceEquiv e).1).pairing :=
      layout.physicalComponentPairing_eq_local S F hconnected e

/-- The **actual physical graph component** and its independently assigned
connected Wick block have the same increasing flattened-leg order.  The
comparison passes through the physically restricted component-leg fiber,
not a formal replacement of the component by an assumed local diagram.
This proves strict monotonicity of the specific equivalence used in
`physicalComponentCanonicalPairing_eq_local`. -/
theorem ExternalInsertionBlockLayout.physicalComponentCanonicalLegEquiv_strictMono
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
     StrictMono ((d.componentBlockLegEquiv C).symm.trans
       (layout.physicalComponentLegEquiv S F hconnected e))) := by
  classical
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  let c := (d.componentBlockLegEquiv C).symm.trans
    (layout.physicalComponentLegEquiv S F hconnected e)
  change StrictMono c
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
  apply lt_of_not_ge
  intro hge
  have hcontra := hlocal.monotone hge
  rw [hbridge j, hbridge i] at hcontra
  exact (not_le_of_gt hglobal) hcontra

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
no residual permutation: the earlier strict-monotonicity proof and the
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
  have hc : StrictMono c :=
    layout.physicalComponentCanonicalLegEquiv_strictMono S F hconnected e
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

/-- Restricting an assembled physical connected component preserves
the original interaction-vertex label at every assigned ambient vertex.
The membership in the *actual* graph-component interaction sector is
derived from preconnected local blocks, not postulated. This is the
vertex-label half of physical component/local Wick-block compatibility. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_restrictComponent_vertexLabel_external
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E))
    (v : ↥(layout.interactionBlock S (layout.sourceEquiv e).1)) :
    ((layout.assembleDiagram S F).restrictComponent
      ⟨(layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e),
        (layout.assembleDiagram S F).vertexGraph.componentBlock_mem_componentPartition
          (Sum.inl e)⟩).vertexLabel
      ⟨v.1, by
        rw [layout.assembleDiagram_componentInteractionSector_external S F hconnected e]
        exact v.2⟩ =
      (F (layout.sourceEquiv e).1).vertexLabel v := by
  classical
  have hidx :
      ((layout.interactionEquiv S).symm
        ⟨(layout.sourceEquiv e).1, v⟩ : ↥S) =
        ⟨v.1, (Finset.mem_filter.mp v.2).1⟩ := by
    apply Subtype.ext
    rfl
  have hlabel :=
    layout.assembleDiagram_vertexLabel S F (layout.sourceEquiv e).1 v
  rw [hidx] at hlabel
  exact hlabel

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
  exact (layout.assembleDiagram_restrictComponent_vertexLabel_external
    S F hconnected e v).symm

/-- Every actual connected component of an independently assembled
diagram has exactly the interaction-vertex weight of its supplied local
Wick block. The equality uses physical graph-component restriction and
the equality of its *actual* interaction-label family, rather than a
postulated split of the vertex product. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_restrictComponent_vertexWeight_external
    {ExternalLabel InternalLabel : Type*}
    {M : Type*} [CommMonoid M]
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (g : InternalLabel → M) (e : Fin (2 * E)) :
    ((layout.assembleDiagram S F).restrictComponent
      ⟨(layout.assembleDiagram S F).vertexGraph.componentBlock (Sum.inl e),
        (layout.assembleDiagram S F).vertexGraph.componentBlock_mem_componentPartition
          (Sum.inl e)⟩).vertexWeight g =
      (F (layout.sourceEquiv e).1).vertexWeight g := by
  classical
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  have hsec :
      interactionSector (C : Finset (ExternalInsertionVertex E S)) =
        layout.interactionBlock S B :=
    layout.assembleDiagram_componentInteractionSector_external S F hconnected e
  let fiberEquiv :
      ↥(interactionSector (C : Finset (ExternalInsertionVertex E S))) ≃
        ↥(layout.interactionBlock S B) :=
    { toFun := fun v => ⟨v.1, by rw [← hsec]; exact v.2⟩
      invFun := fun v => ⟨v.1, by rw [hsec]; exact v.2⟩
      left_inv := fun v => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }
  have hpoint (v : ↥(interactionSector (C : Finset (ExternalInsertionVertex E S)))) :
      (d.restrictComponent C).vertexLabel v = (F B).vertexLabel (fiberEquiv v) := by
    have hv := layout.assembleDiagram_restrictComponent_vertexLabel_external
      S F hconnected e (fiberEquiv v)
    convert hv using 1
  change (∏ v : ↥(interactionSector (C : Finset (ExternalInsertionVertex E S))),
      g ((d.restrictComponent C).vertexLabel v)) =
    ∏ v : ↥(layout.interactionBlock S B), g ((F B).vertexLabel v)
  calc
    _ = ∏ v : ↥(interactionSector (C : Finset (ExternalInsertionVertex E S))),
        g ((F B).vertexLabel (fiberEquiv v)) := by
          apply Finset.prod_congr rfl
          intro v _
          rw [hpoint v]
    _ = _ := Equiv.prod_comp fiberEquiv (fun v => g ((F B).vertexLabel v))

end Common
end SecondQuantization
