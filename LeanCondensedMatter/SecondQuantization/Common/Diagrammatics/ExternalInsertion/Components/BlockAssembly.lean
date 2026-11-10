import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Reassembling external-insertion diagrams over independent external blocks

An externally even partition and an assignment of interaction vertices to its
blocks determine an actual disjoint decomposition of *all flattened legs*.
Unlike restricting the components of a pre-existing diagram, this construction
starts from the external source partition and an independent interaction-slot
assignment. It is statistics-independent.

For preconnected local vertex graphs, the assembled pairing has exactly the
prescribed external-component partition. Conversely, a vacuum-free physical
diagram with a chosen external anchor determines a block layout whose
restrictions reassemble the original labels and pairing.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- Independent assembly data: every external block has even cardinality,
and each interaction vertex is assigned to exactly one external block.
This covers precisely the vacuum-free block layouts needed for the
nonempty-even external-source moment formula. -/
structure ExternalInsertionBlockLayout (E N : ℕ) where
  /-- Prescribed partition of all external fermion slots. -/
  partition : Finpartition (Finset.univ : Finset (Fin (2 * E)))
  /-- Physical pairing parity: each external block contains an even number of legs. -/
  evenBlocks : ∀ B : partition.parts, Even (B : Finset (Fin (2 * E))).card
  /-- Assignment of ambient interaction vertices to external partition blocks. -/
  interactionOwner : Fin N → partition.parts

variable {E N : ℕ}

/-- The interaction vertices assigned to a particular external block. -/
noncomputable def ExternalInsertionBlockLayout.interactionBlock
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (B : layout.partition.parts) : Finset (Fin N) := by
  classical
  exact S.filter (fun v => layout.interactionOwner v = B)

/-- Canonical increasing external source slots, grouped by a partition into
independent even-sized blocks. -/
noncomputable def ExternalInsertionBlockLayout.sourceEquiv
    (layout : ExternalInsertionBlockLayout E N) :
    Fin (2 * E) ≃
      Σ B : layout.partition.parts,
        Fin (2 * ((B : Finset (Fin (2 * E))).card / 2)) := by
  classical
  let full : Fin (2 * E) ≃ ↥(Finset.univ : Finset (Fin (2 * E))) := {
    toFun := fun e => ⟨e, Finset.mem_univ e⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => Subtype.ext rfl
  }
  refine (full.trans layout.partition.equivSigmaParts).trans ?_
  exact Equiv.sigmaCongrRight (fun B =>
    ((B.1.orderIsoOfFin
      (Nat.two_mul_div_two_of_even (layout.evenBlocks B)).symm).symm).toEquiv)

/-- Any assignment of interaction vertices to external blocks partitions
the interaction sector exactly, including empty local interaction sectors. -/
noncomputable def ExternalInsertionBlockLayout.interactionEquiv
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    ↥S ≃ Σ B : layout.partition.parts, ↥(layout.interactionBlock S B) := by
  classical
  let fiberEquiv : ∀ B : layout.partition.parts,
      {v : ↥S // layout.interactionOwner v.1 = B} ≃
        ↥(layout.interactionBlock S B) := fun B => {
    toFun := fun v => ⟨v.1.1, Finset.mem_filter.mpr ⟨v.1.2, v.2⟩⟩
    invFun := fun v =>
      ⟨⟨v.1, (Finset.mem_filter.mp v.2).1⟩,
        (Finset.mem_filter.mp v.2).2⟩
    left_inv := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro v
      apply Subtype.ext
      rfl
  }
  exact (Equiv.sigmaFiberEquiv
    (fun v : ↥S => layout.interactionOwner v.1)).symm.trans
      (Equiv.sigmaCongrRight fiberEquiv)

/-- Distribute a disjoint union of dependent families across their common
index. This is the sum analogue of `Equiv.sigmaProdDistrib`. -/
private def sumSigmaEquiv {ι : Type*} {α β : ι → Type*} :
    ((Σ i, α i) ⊕ (Σ i, β i)) ≃ Σ i, α i ⊕ β i where
  toFun
    | Sum.inl ⟨i, x⟩ => ⟨i, Sum.inl x⟩
    | Sum.inr ⟨i, x⟩ => ⟨i, Sum.inr x⟩
  invFun
    | ⟨i, Sum.inl x⟩ => Sum.inl ⟨i, x⟩
    | ⟨i, Sum.inr x⟩ => Sum.inr ⟨i, x⟩
  left_inv := by
    intro x
    rcases x with (⟨i, x⟩ | ⟨i, x⟩) <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨i, (x | x)⟩ <;> rfl

/-- A **concrete** equivalence between the full flattened legs and the
disjoint union of each independently specified external block's flattened
legs. Both external-slot order and interaction-vertex identity are retained. -/
noncomputable def ExternalInsertionBlockLayout.legEquiv
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card + E)) ≃
      Σ B : layout.partition.parts,
        Fin (2 * (2 * (layout.interactionBlock S B).card +
          ((B : Finset (Fin (2 * E))).card / 2))) := by
  classical
  let eExt := layout.sourceEquiv
  let eInt : (↥S × Fin 4) ≃
      Σ B : layout.partition.parts,
        ↥(layout.interactionBlock S B) × Fin 4 :=
    ((layout.interactionEquiv S).prodCongr (Equiv.refl (Fin 4))).trans
      (Equiv.sigmaProdDistrib
        (fun B : layout.partition.parts => ↥(layout.interactionBlock S B)) (Fin 4))
  let eSum := Equiv.sumCongr eExt eInt
  let eSigma : ((Σ B : layout.partition.parts,
        Fin (2 * ((B : Finset (Fin (2 * E))).card / 2))) ⊕
      (Σ B : layout.partition.parts,
        ↥(layout.interactionBlock S B) × Fin 4)) ≃
      Σ B : layout.partition.parts,
        Fin (2 * ((B : Finset (Fin (2 * E))).card / 2)) ⊕
          (↥(layout.interactionBlock S B) × Fin 4) := sumSigmaEquiv
  exact ((externalInsertionLegEquiv E S).trans eSum).trans <|
    eSigma.trans (Equiv.sigmaCongrRight (fun B =>
      (externalInsertionLegEquiv
        ((B : Finset (Fin (2 * E))).card / 2)
        (layout.interactionBlock S B)).symm))

/-- The exact vertex analogue of `legEquiv`. Both source insertions
and ambient interaction vertices are assigned to the same independent
external block as their incident legs. -/
noncomputable def ExternalInsertionBlockLayout.vertexEquiv
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    ExternalInsertionVertex E S ≃
      Σ B : layout.partition.parts,
        ExternalInsertionVertex
          ((B : Finset (Fin (2 * E))).card / 2) (layout.interactionBlock S B) :=
  (Equiv.sumCongr layout.sourceEquiv (layout.interactionEquiv S)).trans
    sumSigmaEquiv

@[simp]
theorem ExternalInsertionBlockLayout.vertexEquiv_external
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (e : Fin (2 * E)) :
    layout.vertexEquiv S (Sum.inl e) =
      ⟨(layout.sourceEquiv e).1, Sum.inl (layout.sourceEquiv e).2⟩ := by
  rfl

@[simp]
theorem ExternalInsertionBlockLayout.vertexEquiv_interaction
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (v : ↥S) :
    layout.vertexEquiv S (Sum.inr v) =
      ⟨(layout.interactionEquiv S v).1,
        Sum.inr (layout.interactionEquiv S v).2⟩ := by
  rfl

/-- The leg equivalence assigns each external insertion to its exact
source-partition block, retaining its increasing local external slot. -/
@[simp]
theorem ExternalInsertionBlockLayout.legEquiv_externalLeg
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (e : Fin (2 * E)) :
    layout.legEquiv S (externalInsertionExternalLeg E S e) =
      ⟨(layout.sourceEquiv e).1,
        externalInsertionExternalLeg
          ((layout.sourceEquiv e).1.1.card / 2)
          (layout.interactionBlock S (layout.sourceEquiv e).1)
          (layout.sourceEquiv e).2⟩ := by
  simp [ExternalInsertionBlockLayout.legEquiv, externalInsertionExternalLeg,
    sumSigmaEquiv]

/-- The leg equivalence assigns each quartic leg to its vertex's block,
without changing the quartic local leg index. -/
@[simp]
theorem ExternalInsertionBlockLayout.legEquiv_interactionLeg
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (v : ↥S) (i : Fin 4) :
    layout.legEquiv S (externalInsertionInteractionLeg (E := E) v i) =
      ⟨(layout.interactionEquiv S v).1,
        externalInsertionInteractionLeg
          (E := ((layout.interactionEquiv S v).1.1.card / 2))
          (layout.interactionEquiv S v).2 i⟩ := by
  simp [ExternalInsertionBlockLayout.legEquiv, externalInsertionInteractionLeg,
    sumSigmaEquiv]

/-- A leg and its incident vertex have exactly the same independent
external-block owner. More strongly, the vertex inside that block is
preserved by the two canonical equivalences. -/
theorem ExternalInsertionBlockLayout.vertexEquiv_vertexOfLeg
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (leg : Fin (2 * (2 * S.card + E))) :
    layout.vertexEquiv S (externalInsertionVertexOfLeg leg) =
      ⟨(layout.legEquiv S leg).1,
        externalInsertionVertexOfLeg (layout.legEquiv S leg).2⟩ := by
  classical
  cases hleg : externalInsertionLegEquiv E S leg with
  | inl e =>
    have heq : leg = externalInsertionExternalLeg E S e := by
      apply (externalInsertionLegEquiv E S).injective
      simpa [externalInsertionExternalLeg] using hleg
    rw [heq]
    rw [layout.legEquiv_externalLeg]
    simp
  | inr p =>
    obtain ⟨v, i⟩ := p
    have heq : leg = externalInsertionInteractionLeg (E := E) v i := by
      apply (externalInsertionLegEquiv E S).injective
      simpa [externalInsertionInteractionLeg] using hleg
    rw [heq]
    rw [layout.legEquiv_interactionLeg]
    simp

/-- Assemble a labelled Wick diagram from **independent, block-local**
external-insertion diagrams.

The external source slots are assigned to blocks in increasing source order,
and interaction vertices retain their original ambient labels. The pairing is
the disjoint union of the chosen local pairings, transported along the
concrete flattened-leg equivalence above.

This defines a physical pairing; identifying its connected-component
partition with the *given* external partition additionally requires that
each chosen block diagram is fully connected. -/
noncomputable def ExternalInsertionBlockLayout.assembleDiagram
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N S where
  externalLabel e :=
    (F (layout.sourceEquiv e).1).externalLabel (layout.sourceEquiv e).2
  vertexLabel v :=
    (F (layout.interactionEquiv S v).1).vertexLabel (layout.interactionEquiv S v).2
  pairing :=
    (Combinatorics.PairingOn.sigmaCongrRight (fun B => (F B).pairing)).transport
      (layout.legEquiv S)

/-- The assembled external field labels are exactly the independently
specified block labels in their canonical increasing source order. -/
@[simp]
theorem ExternalInsertionBlockLayout.assembleDiagram_externalLabel
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (B : layout.partition.parts)
    (i : Fin (2 * ((B : Finset (Fin (2 * E))).card / 2))) :
    (layout.assembleDiagram S F).externalLabel
        (layout.sourceEquiv.symm ⟨B, i⟩) = (F B).externalLabel i := by
  change (F (layout.sourceEquiv (layout.sourceEquiv.symm ⟨B, i⟩)).1).externalLabel
    (layout.sourceEquiv (layout.sourceEquiv.symm ⟨B, i⟩)).2 = _
  rw [Equiv.apply_symm_apply]

/-- The assembled interaction labels are exactly the independently
specified block labels, at their original ambient interaction vertices. -/
@[simp]
theorem ExternalInsertionBlockLayout.assembleDiagram_vertexLabel
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (B : layout.partition.parts) (v : ↥(layout.interactionBlock S B)) :
    (layout.assembleDiagram S F).vertexLabel
        ((layout.interactionEquiv S).symm ⟨B, v⟩) = (F B).vertexLabel v := by
  change (F ((layout.interactionEquiv S) ((layout.interactionEquiv S).symm ⟨B, v⟩)).1).vertexLabel
    ((layout.interactionEquiv S) ((layout.interactionEquiv S).symm ⟨B, v⟩)).2 = _
  rw [Equiv.apply_symm_apply]

/-- An assembled pairing stays in the specified external block on both
ends of every pair, and its within-block partner is the original local
pairing partner. This is the independent-block counterpart of the
component-restriction partner theorem. -/
@[simp]
theorem ExternalInsertionBlockLayout.assembleDiagram_partner
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (B : layout.partition.parts)
    (i : Fin (2 * (2 * (layout.interactionBlock S B).card +
      ((B : Finset (Fin (2 * E))).card / 2)))) :
    (layout.assembleDiagram S F).pairing.partner
        ((layout.legEquiv S).symm ⟨B, i⟩) =
      (layout.legEquiv S).symm ⟨B, (F B).pairing.partner i⟩ := by
  simp [ExternalInsertionBlockLayout.assembleDiagram]


/-- A paired leg in the assembled diagram remains in its original
external block. This rules out propagators between independently assembled
blocks, including blocks with no interaction vertices. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_partner_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (leg : Fin (2 * (2 * S.card + E))) :
    (layout.legEquiv S ((layout.assembleDiagram S F).pairing.partner leg)).1 =
      (layout.legEquiv S leg).1 := by
  change (layout.legEquiv S
    (((PairingOn.sigmaCongrRight (fun B => (F B).pairing)).transport
      (layout.legEquiv S)).partner leg)).1 = _
  rw [PairingOn.transport_partner, Equiv.apply_symm_apply]
  cases h : layout.legEquiv S leg with
  | mk B i =>
    simp only [PairingOn.sigmaCongrRight_partner]

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
      (layout.assembleDiagram_partner_block S F) B) = F := by
  apply layout.assembleDiagram_injective S
  exact layout.assembleDiagram_restrictBlock S
    (layout.assembleDiagram S F) (layout.assembleDiagram_partner_block S F)


/-- The complete family of block-local labelled pairings is equivalent
to the global labelled diagrams whose propagators respect the prescribed
external-block layout. Both sides retain every external/interaction label
and every pairing partner. -/
noncomputable def ExternalInsertionBlockLayout.assemblyEquivBlockRespecting
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    (∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      ∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1} where
  toFun F := ⟨layout.assembleDiagram S F, layout.assembleDiagram_partner_block S F⟩
  invFun d := layout.restrictBlock S d.1 d.2
  left_inv F := layout.restrictBlock_assembleDiagram S F
  right_inv d := by
    apply Subtype.ext
    exact layout.assembleDiagram_restrictBlock S d.1 d.2

/-- The block-assembly equivalence recovers the *exact* original physical
diagram from the inverse image, rather than only its connected partition. -/
@[simp]
theorem ExternalInsertionBlockLayout.assemblyEquivBlockRespecting_apply
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) :
    (layout.assemblyEquivBlockRespecting S F).1 = layout.assembleDiagram S F :=
  rfl

/-- Reindex *any* finite weighted sum of block-respecting physical
diagrams by their independent local labelled diagrams. This is the
diagram-pairing sum conversion underlying fixed-order Dyson-fiber sums;
the integrand can be the physical integrated amplitude itself. -/
theorem ExternalInsertionBlockLayout.sum_blockRespecting_eq_sum_local
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
        ∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
          (layout.legEquiv S leg).1}, weight d.1) =
      ∑ F : ∀ B : layout.partition.parts,
          ExternalInsertionDiagram ExternalLabel InternalLabel
            ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B),
        weight (layout.assembleDiagram S F) := by
  classical
  simpa only [layout.assemblyEquivBlockRespecting_apply] using
    (Equiv.sum_comp (layout.assemblyEquivBlockRespecting S)
      (fun d => weight d.1)).symm

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
    have he := congrFun (h (layout.sourceEquiv e).1)
      (layout.sourceEquiv e).2
    change (F (layout.sourceEquiv e).1).externalLabel
      (layout.sourceEquiv e).2 = labels e
    change (F (layout.sourceEquiv e).1).externalLabel
      (layout.sourceEquiv e).2 =
        labels (layout.sourceEquiv.symm (layout.sourceEquiv e)) at he
    simpa only [Equiv.symm_apply_apply] using he

/-- Blockwise assembly remains an exact equivalence after *fixing* the
external field labels. Only internal vertex labels and the Wick pairing
are allowed to vary in each finite Dyson coefficient. -/
noncomputable def ExternalInsertionBlockLayout.assemblyEquivBlockRespectingFixedLabels
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (labels : Fin (2 * E) → ExternalLabel) :
    {F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) //
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)} ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      (∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) ∧ d.externalLabel = labels} where
  toFun F :=
    ⟨layout.assembleDiagram S F.1,
      layout.assembleDiagram_partner_block S F.1,
      (layout.assembleDiagram_externalLabel_eq_iff S F.1 labels).2 F.2⟩
  invFun d :=
    ⟨layout.restrictBlock S d.1 d.2.1,
      (layout.assembleDiagram_externalLabel_eq_iff S
        (layout.restrictBlock S d.1 d.2.1) labels).1 (by
          rw [layout.assembleDiagram_restrictBlock S d.1 d.2.1]
          exact d.2.2)⟩
  left_inv F := by
    apply Subtype.ext
    exact layout.restrictBlock_assembleDiagram S F.1
  right_inv d := by
    apply Subtype.ext
    exact layout.assembleDiagram_restrictBlock S d.1 d.2.1

/-- The fixed-label equivalence preserves the assembled diagram itself. -/
@[simp]
theorem ExternalInsertionBlockLayout.assemblyEquivBlockRespectingFixedLabels_apply
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (labels : Fin (2 * E) → ExternalLabel)
    (F : {F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) //
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)}) :
    (layout.assemblyEquivBlockRespectingFixedLabels S labels F).1 =
      layout.assembleDiagram S F.1 := rfl

open Classical in
/-- Finite weighted fixed-external-label diagram sums can be reindexed
over independently chosen local labels and pairings with those exact
external field labels. In particular, the weight may be the integrated
Dyson amplitude at one fixed perturbative order. -/
theorem ExternalInsertionBlockLayout.sum_blockRespectingFixedLabels_eq_sum_local
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (labels : Fin (2 * E) → ExternalLabel)
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      (∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) ∧ d.externalLabel = labels}, weight d.1) =
    ∑ F : {F : ∀ B : layout.partition.parts,
        ExternalInsertionDiagram ExternalLabel InternalLabel
          ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) //
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)},
        weight (layout.assembleDiagram S F.1) := by
  classical
  simpa only [layout.assemblyEquivBlockRespectingFixedLabels_apply] using
    (Equiv.sum_comp (layout.assemblyEquivBlockRespectingFixedLabels S labels)
      (fun d => weight d.1)).symm

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



/-- The active interaction sectors assigned to an external partition form
an exact disjoint decomposition of the global interaction sector. In
particular, empty local interaction blocks contribute zero to this sum. -/
theorem ExternalInsertionBlockLayout.sum_interactionBlock_card_eq
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    (∑ B : layout.partition.parts, (layout.interactionBlock S B).card) = S.card := by
  classical
  have h := Fintype.card_congr (layout.interactionEquiv S)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

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

/-- Connected independent labelled blocks over all ambient interaction
slots. Every block is required to be preconnected, so the assembled
diagram has no disconnected vacuum component. -/
abbrev ExternalInsertionBlockLayout.ConnectedBlockFamily
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) :=
  {F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
    ∀ B, (F B).vertexGraph.Preconnected}

/-- Assemble a dependent family of connected external blocks into its
vacuum-free labelled physical diagram. -/
noncomputable def ExternalInsertionBlockLayout.assembleConnectedBlockFamily
    {ExternalLabel InternalLabel : Type*}
    (p : Σ layout : ExternalInsertionBlockLayout E N,
      layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} :=
  ⟨p.1.assembleDiagram (Finset.univ : Finset (Fin N)) p.2.1,
    p.1.hasNoVacuumComponent_assembleDiagram
      (Finset.univ : Finset (Fin N)) p.2.1 p.2.2⟩

/-- Connected block assembly is injective: the physical connected graph
recovers the exact external layout, and the assembly map recovers all
local pairing and label data. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlockFamily_injective
    {ExternalLabel InternalLabel : Type*} (anchor : Fin (2 * E)) :
    Function.Injective (ExternalInsertionBlockLayout.assembleConnectedBlockFamily
      (E := E) (N := N) (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel)) := by
  intro x y h
  rcases x with ⟨layoutX, ⟨FX, hX⟩⟩
  rcases y with ⟨layoutY, ⟨FY, hY⟩⟩
  have hdiagram :
      layoutX.assembleDiagram (Finset.univ : Finset (Fin N)) FX =
        layoutY.assembleDiagram (Finset.univ : Finset (Fin N)) FY :=
    congrArg Subtype.val h
  have hphysical :
      (layoutX.assembleDiagram (Finset.univ : Finset (Fin N)) FX).externalBlockLayout
          (layoutX.hasNoVacuumComponent_assembleDiagram
            (Finset.univ : Finset (Fin N)) FX hX) anchor =
        (layoutY.assembleDiagram (Finset.univ : Finset (Fin N)) FY).externalBlockLayout
          (layoutY.hasNoVacuumComponent_assembleDiagram
            (Finset.univ : Finset (Fin N)) FY hY) anchor :=
    ExternalInsertionDiagram.externalBlockLayout_congr hdiagram _ _ anchor
  have hlayout : layoutX = layoutY := by
    calc
      layoutX =
          (layoutX.assembleDiagram (Finset.univ : Finset (Fin N)) FX).externalBlockLayout
            (layoutX.hasNoVacuumComponent_assembleDiagram
              (Finset.univ : Finset (Fin N)) FX hX) anchor :=
        (layoutX.externalBlockLayout_assembleDiagram_eq FX hX anchor).symm
      _ = _ := hphysical
      _ = layoutY := layoutY.externalBlockLayout_assembleDiagram_eq FY hY anchor
  cases hlayout
  have hfam : FX = FY :=
    layoutX.assembleDiagram_injective (Finset.univ : Finset (Fin N)) hdiagram
  cases hfam
  rfl

/-- Any vacuum-free physical diagram is assembled from its actual external
component layout and the connected local diagrams obtained by restriction. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlockFamily_surjective
    {ExternalLabel InternalLabel : Type*} (anchor : Fin (2 * E)) :
    Function.Surjective (ExternalInsertionBlockLayout.assembleConnectedBlockFamily
      (E := E) (N := N) (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel)) := by
  intro d
  rcases d with ⟨d, hVac⟩
  let layout := d.externalBlockLayout hVac anchor
  let F := layout.restrictBlock (Finset.univ : Finset (Fin N)) d
    (d.externalBlockLayout_partner_block hVac anchor)
  refine ⟨⟨layout, ⟨F, d.restrictPhysicalBlocks_preconnected hVac anchor⟩⟩, ?_⟩
  apply Subtype.ext
  exact d.assembleDiagram_restrictPhysicalBlocks hVac anchor

/-- A vacuum-free physical diagram has a unique independent-block
description with preconnected local diagrams, including exact interaction
ownership, external labels, vertex labels and Wick pairing partners. -/
noncomputable def ExternalInsertionBlockLayout.connectedAssemblyEquiv
    {ExternalLabel InternalLabel : Type*} (anchor : Fin (2 * E)) :
    (Σ layout : ExternalInsertionBlockLayout E N,
      layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} :=
  Equiv.ofBijective
    (ExternalInsertionBlockLayout.assembleConnectedBlockFamily
      (E := E) (N := N) (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel))
    ⟨ExternalInsertionBlockLayout.assembleConnectedBlockFamily_injective anchor,
      ExternalInsertionBlockLayout.assembleConnectedBlockFamily_surjective anchor⟩


end Common
end SecondQuantization
