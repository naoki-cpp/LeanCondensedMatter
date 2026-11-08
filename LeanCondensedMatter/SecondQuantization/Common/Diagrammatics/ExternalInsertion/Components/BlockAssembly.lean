import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
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

A further connectedness theorem is needed to identify these blocks with the
graph components of the assembled pairing; no such assertion is built into the
layout or the assembly definitions.
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
    simp
  | inr p =>
    obtain ⟨v, i⟩ := p
    have heq : leg = externalInsertionInteractionLeg (E := E) v i := by
      apply (externalInsertionLegEquiv E S).injective
      simpa [externalInsertionInteractionLeg] using hleg
    rw [heq]
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


end Common
end SecondQuantization
