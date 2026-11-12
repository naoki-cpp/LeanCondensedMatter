import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport
import LeanCondensedMatter.Combinatorics.Shuffle.FamilyOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
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

/-- The inverse block source equivalence is the canonical increasing
enumeration of the partition block. In particular, component restriction
does not introduce an additional permutation of the fermionic source legs. -/
theorem ExternalInsertionBlockLayout.sourceEquiv_symm_apply
    (layout : ExternalInsertionBlockLayout E N)
    (B : layout.partition.parts)
    (i : Fin (2 * ((B : Finset (Fin (2 * E))).card / 2))) :
    layout.sourceEquiv.symm ⟨B, i⟩ =
      ((B.1.orderIsoOfFin
        (Nat.two_mul_div_two_of_even (layout.evenBlocks B)).symm) i).1 := by
  rfl

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

/-- An independently assigned local external leg is embedded at its
original ambient source slot, in increasing source-partition order. -/
theorem ExternalInsertionBlockLayout.legEquiv_symm_externalLeg
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (B : layout.partition.parts)
    (i : Fin (2 * ((B : Finset (Fin (2 * E))).card / 2))) :
    (layout.legEquiv S).symm
      ⟨B, externalInsertionExternalLeg
        ((B : Finset (Fin (2 * E))).card / 2)
        (layout.interactionBlock S B) i⟩ =
      externalInsertionExternalLeg E S (layout.sourceEquiv.symm ⟨B, i⟩) := by
  apply (layout.legEquiv S).injective
  rw [Equiv.apply_symm_apply, layout.legEquiv_externalLeg,
    Equiv.apply_symm_apply]

/-- An independently assigned local quartic leg is embedded at the
same physical interaction vertex and with the same four-leg index. -/
theorem ExternalInsertionBlockLayout.legEquiv_symm_interactionLeg
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (B : layout.partition.parts)
    (v : ↥(layout.interactionBlock S B)) (i : Fin 4) :
    (layout.legEquiv S).symm
      ⟨B, externalInsertionInteractionLeg
        (E := ((B : Finset (Fin (2 * E))).card / 2)) v i⟩ =
      externalInsertionInteractionLeg (E := E)
        ((layout.interactionEquiv S).symm ⟨B, v⟩) i := by
  apply (layout.legEquiv S).injective
  rw [Equiv.apply_symm_apply, layout.legEquiv_interactionLeg,
    Equiv.apply_symm_apply]

/-- Every independent local Wick block embeds its **entire** flattened
fermion-leg sequence in strictly increasing ambient order. This is
stronger than preserving source insertion order alone: it preserves
the relative order of all quartic legs, including blocks without
interaction vertices. -/
theorem ExternalInsertionBlockLayout.blockLegEmbedding_strictMono
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (B : layout.partition.parts) :
    StrictMono (fun p : Fin (2 * (2 * (layout.interactionBlock S B).card +
        ((B : Finset (Fin (2 * E))).card / 2))) =>
      (layout.legEquiv S).symm ⟨B, p⟩) := by
  classical
  let T := layout.interactionBlock S B
  let localEquiv := externalInsertionLegEquiv (B.1.card / 2) T
  intro a b hab
  obtain ⟨la, rfl⟩ := localEquiv.symm.surjective a
  obtain ⟨lb, rfl⟩ := localEquiv.symm.surjective b
  rcases la with e | ⟨v, l⟩ <;> rcases lb with f | ⟨w, k⟩
  · change
      (externalInsertionExternalLeg (B.1.card / 2) T e).val <
        (externalInsertionExternalLeg (B.1.card / 2) T f).val at hab
    rw [layout.legEquiv_symm_externalLeg S B e,
      layout.legEquiv_symm_externalLeg S B f]
    change (layout.sourceEquiv.symm ⟨B, e⟩).val <
      (layout.sourceEquiv.symm ⟨B, f⟩).val
    rw [layout.sourceEquiv_symm_apply B e,
      layout.sourceEquiv_symm_apply B f]
    have hef : e < f := by simpa using hab
    exact (B.1.orderIsoOfFin
      (Nat.two_mul_div_two_of_even (layout.evenBlocks B)).symm).strictMono hef
  · rw [layout.legEquiv_symm_externalLeg S B e,
      layout.legEquiv_symm_interactionLeg S B w k]
    change
      (externalInsertionExternalLeg E S (layout.sourceEquiv.symm ⟨B, e⟩)).val <
      (externalInsertionInteractionLeg (E := E)
        ((layout.interactionEquiv S).symm ⟨B, w⟩) k).val
    simp only [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
    have hbound := (layout.sourceEquiv.symm ⟨B, e⟩).isLt
    omega
  · change
      (externalInsertionInteractionLeg (E := B.1.card / 2) v l).val <
        (externalInsertionExternalLeg (B.1.card / 2) T f).val at hab
    simp at hab
  · rw [layout.legEquiv_symm_interactionLeg S B v l,
      layout.legEquiv_symm_interactionLeg S B w k]
    change
      (externalInsertionInteractionLeg (E := E)
        ((layout.interactionEquiv S).symm ⟨B, v⟩) l).val <
      (externalInsertionInteractionLeg (E := E)
        ((layout.interactionEquiv S).symm ⟨B, w⟩) k).val
    change
      (externalInsertionInteractionLeg (E := B.1.card / 2) v l).val <
      (externalInsertionInteractionLeg (E := B.1.card / 2) w k).val at hab
    simp only [externalInsertionInteractionLeg_val] at hab ⊢
    have hv (u : ↥T) :
        ((layout.interactionEquiv S).symm ⟨B, u⟩ : ↥S) =
          ⟨u.1, (Finset.mem_filter.mp u.2).1⟩ := by
      apply Subtype.ext
      rfl
    rw [hv v, hv w]
    by_cases hvw : v = w
    · subst w
      omega
    · have hrank_ne :
          ((T.orderIsoOfFin rfl).symm v).val ≠
            ((T.orderIsoOfFin rfl).symm w).val :=
        fun h => hvw ((T.orderIsoOfFin rfl).symm.injective (Fin.ext h))
      have hrank :
          ((T.orderIsoOfFin rfl).symm v).val <
            ((T.orderIsoOfFin rfl).symm w).val := by
        have hl := l.isLt
        have hk := k.isLt
        omega
      have hamb :
          ((S.orderIsoOfFin rfl).symm
            (⟨v.1, (Finset.mem_filter.mp v.2).1⟩ : ↥S)).val <
          ((S.orderIsoOfFin rfl).symm
            (⟨w.1, (Finset.mem_filter.mp w.2).1⟩ : ↥S)).val := by
        apply (S.orderIsoOfFin rfl).symm.strictMono
        change v.1 < w.1
        simpa using (T.orderIsoOfFin rfl).strictMono hrank
      have hl := l.isLt
      have hk := k.isLt
      omega

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

/-- An assembled Wick diagram retains the *actual quartic interaction
label* at each local vertex when the ambient order is decomposed into
block-local orders and its order-preserving shuffle. This is the
vertex-label transport needed in the ordered Dyson integrand. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_vertexLabel_at_shuffledSlot
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
      (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩)) =
        (F B).vertexLabel ((layout.interactionOrderDecompositionEquiv order).1 B j) := by
  rw [layout.interactionOrderDecomposition_slotVertex order B j]
  exact layout.assembleDiagram_vertexLabel
    (Finset.univ : Finset (Fin N)) F B
    ((layout.interactionOrderDecompositionEquiv order).1 B j)

/-- Every product of physical quartic-vertex labels factors into the
products on the independently assembled blocks, with the exact local
vertex orders induced by any global Dyson time order. No permutation
multiplicity is introduced by the shuffle. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_vertexLabel_orderProduct
    {ExternalLabel InternalLabel M : Type*} [CommMonoid M]
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (g : InternalLabel → M)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N))) :
    (∏ j : Fin (Finset.univ : Finset (Fin N)).card,
      g ((layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
        (order j))) =
      ∏ B : layout.partition.parts,
        ∏ j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card,
          g ((F B).vertexLabel ((layout.interactionOrderDecompositionEquiv order).1 B j)) := by
  classical
  let shuffle := (layout.interactionOrderDecompositionEquiv order).2
  calc
    (∏ j : Fin (Finset.univ : Finset (Fin N)).card,
      g ((layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
        (order j))) =
      ∏ z : Σ B : layout.partition.parts,
        Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card,
        g ((layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
          (order (shuffle.slotEquiv z))) := by
        exact (Equiv.prod_comp shuffle.slotEquiv
          (fun j => g ((layout.assembleDiagram
            (Finset.univ : Finset (Fin N)) F).vertexLabel (order j)))).symm
    _ = ∏ B : layout.partition.parts,
        ∏ j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card,
          g ((F B).vertexLabel
            ((layout.interactionOrderDecompositionEquiv order).1 B j)) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro B _
      apply Finset.prod_congr rfl
      intro j _
      exact congrArg g
        (layout.assembleDiagram_vertexLabel_at_shuffledSlot F order B j)

/-- A time attached to the global ordered-simplex slot of a
block-local interaction vertex is exactly the time pulled back along
the ambient interaction order to that vertex. No numerical re-sorting
of external insertion times is involved. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_localTime
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (τ : Fin (Finset.univ : Finset (Fin N)).card → ℝ)
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    τ ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩) =
      τ (order.symm ((layout.interactionEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (layout.interactionOrderDecompositionEquiv order).1 B j⟩)) := by
  have h := congrArg (fun v : ↥(Finset.univ : Finset (Fin N)) =>
    τ (order.symm v)) (layout.interactionOrderDecomposition_slotVertex order B j)
  simpa only [Equiv.symm_apply_apply] using h

/-- In a physically assembled Wick diagram, the actual global partner
of any quartic leg at a shuffled interaction slot is precisely the
inverse-leg transport of its original block-local partner. In particular,
no propagator can cross between source-partition blocks after any
interaction-time interleaving. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_partner_at_shuffledInteractionLeg
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
    (i : Fin 4) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).pairing.partner
      (externalInsertionInteractionLeg (E := E)
        (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv
          ⟨B, j⟩)) i) =
      (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (F B).pairing.partner
          (externalInsertionInteractionLeg
            (E := (B : Finset (Fin (2 * E))).card / 2)
            ((layout.interactionOrderDecompositionEquiv order).1 B j) i)⟩ := by
  classical
  have hleg :
      layout.legEquiv (Finset.univ : Finset (Fin N))
        (externalInsertionInteractionLeg (E := E)
          (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv
            ⟨B, j⟩)) i) =
        ⟨B, externalInsertionInteractionLeg
          (E := (B : Finset (Fin (2 * E))).card / 2)
          ((layout.interactionOrderDecompositionEquiv order).1 B j) i⟩ := by
    rw [layout.interactionOrderDecomposition_slotVertex order B j]
    rw [layout.legEquiv_interactionLeg]
    rw [(layout.interactionEquiv (Finset.univ : Finset (Fin N))).apply_symm_apply]
  have hglobal :
      externalInsertionInteractionLeg (E := E)
          (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv
            ⟨B, j⟩)) i =
        (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
          ⟨B, externalInsertionInteractionLeg
            (E := (B : Finset (Fin (2 * E))).card / 2)
            ((layout.interactionOrderDecompositionEquiv order).1 B j) i⟩ := by
    apply (layout.legEquiv (Finset.univ : Finset (Fin N))).injective
    simpa only [Equiv.apply_symm_apply] using hleg
  rw [hglobal]
  exact layout.assembleDiagram_partner
    (Finset.univ : Finset (Fin N)) F B _

/-- The original partner of an external source leg in an assembled
diagram is the exact transport of the corresponding local external
source leg's partner. Together with the interaction-leg theorem, this
covers both kinds of atomic legs in a connected block. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_partner_at_externalLeg
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (B : layout.partition.parts)
    (i : Fin (2 * ((B : Finset (Fin (2 * E))).card / 2))) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).pairing.partner
      (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N))
        (layout.sourceEquiv.symm ⟨B, i⟩)) =
      (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (F B).pairing.partner
          (externalInsertionExternalLeg
            ((B : Finset (Fin (2 * E))).card / 2)
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) i)⟩ := by
  classical
  have hleg :
      layout.legEquiv (Finset.univ : Finset (Fin N))
        (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N))
          (layout.sourceEquiv.symm ⟨B, i⟩)) =
        ⟨B, externalInsertionExternalLeg
          ((B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) i⟩ := by
    rw [layout.legEquiv_externalLeg]
    have hsource :=
      (layout.sourceEquiv).apply_symm_apply
        (⟨B, i⟩ : Σ C : layout.partition.parts,
          Fin (2 * ((C : Finset (Fin (2 * E))).card / 2)))
    rw [hsource]
  have hglobal :
      externalInsertionExternalLeg E (Finset.univ : Finset (Fin N))
        (layout.sourceEquiv.symm ⟨B, i⟩) =
      (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, externalInsertionExternalLeg
          ((B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) i⟩ := by
    apply (layout.legEquiv (Finset.univ : Finset (Fin N))).injective
    simpa only [Equiv.apply_symm_apply] using hleg
  rw [hglobal]
  exact layout.assembleDiagram_partner
    (Finset.univ : Finset (Fin N)) F B _

/-- Reindex a finite sum over every ambient interaction order by the
independent local block orders and their interleavings, with no
multiplicity or omission even for zero-interaction blocks. -/
theorem ExternalInsertionBlockLayout.sum_interactionOrders_eq_sum_blockOrders_shuffles
    (layout : ExternalInsertionBlockLayout E N)
    {M : Type*} [AddCommMonoid M]
    (weight : QuarticVertexOrder (Finset.univ : Finset (Fin N)) → M) :
    (∑ order : QuarticVertexOrder (Finset.univ : Finset (Fin N)), weight order) =
      ∑ data : FamilyOrdersOf
          (fun B : layout.partition.parts =>
            ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
          (fun B => (layout.interactionBlock
            (Finset.univ : Finset (Fin N)) B).card) ×
          FamilySlotShuffleTo
            (fun B : layout.partition.parts =>
              (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
            (Finset.univ : Finset (Fin N)).card,
        weight (layout.interactionOrderDecompositionEquiv.symm data) := by
  classical
  exact (Equiv.sum_comp layout.interactionOrderDecompositionEquiv.symm weight).symm

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

/-- The global interaction order encoded by the canonical assignment
shuffle and its associated local orders is exactly the original canonical
increasing interaction order. -/
theorem ExternalInsertionBlockLayout.interactionAssignmentShuffle_reassembles
    (layout : ExternalInsertionBlockLayout E N) :
    layout.interactionOrderDecompositionEquiv.symm
      (layout.interactionOrderDecompositionEquiv
        ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv) =
      ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv := by
  exact layout.interactionOrderDecompositionEquiv.symm_apply_apply _

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



/-- Enumerate every independently assigned connected block family by
transporting the finite set of vacuum-free physical diagrams through the
exact assembly equivalence. This requires no arbitrary choice of a
finiteness instance for the dependent layout type. -/
noncomputable def ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
    {ExternalLabel InternalLabel : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (anchor : Fin (2 * E)) :
    Finset (Σ layout : ExternalInsertionBlockLayout E N,
      layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) := by
  classical
  exact (Finset.univ : Finset
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph}).image
      (ExternalInsertionBlockLayout.connectedAssemblyEquiv anchor).symm

open Classical in
/-- Every finite weighted vacuum-free diagram sum is exactly reindexed by
the full dependent family of connected local diagrams and their interaction
vertex assignments. No layout is counted twice, and the weight is evaluated
on the original assembled labelled pairing. -/
theorem ExternalInsertionBlockLayout.sum_vacuumFree_eq_sum_connectedBlockFamilies
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph}, weight d.1) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor,
        weight (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1 := by
  classical
  unfold ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d _
    have h := (ExternalInsertionBlockLayout.connectedAssemblyEquiv
      (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
      anchor).apply_symm_apply d
    exact (congrArg (fun x : {d : ExternalInsertionDiagram
        ExternalLabel InternalLabel E N
          (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph} => weight x.1) h).symm
  · intro x _ y _ h
    exact (ExternalInsertionBlockLayout.connectedAssemblyEquiv
      (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
      anchor).symm.injective h


open Classical in
/-- Reindex one *fixed external-component partition fiber* of the
vacuum-free physical diagram sum by exactly those independent connected
block layouts whose prescribed source partition is the given fiber.
The equality is valid for arbitrary weights and preserves the original
labelled diagram, pairing and interaction-vertex ownership. -/
theorem ExternalInsertionBlockLayout.sum_externalPartitionFiber_eq_sum_connectedBlockFamilies
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph},
      if externalComponentPartition d.1.vertexGraph = π then weight d.1 else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor,
        if p.1.partition = π then
          weight (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
        else 0 := by
  classical
  calc
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph},
      if externalComponentPartition d.1.vertexGraph = π then weight d.1 else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor,
        if externalComponentPartition
            (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1.vertexGraph = π
          then weight (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
          else 0 :=
        ExternalInsertionBlockLayout.sum_vacuumFree_eq_sum_connectedBlockFamilies
          anchor (fun d => if externalComponentPartition d.vertexGraph = π then weight d else 0)
    _ = ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor,
        if p.1.partition = π then
          weight (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
        else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      have hπ :
          externalComponentPartition
            (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1.vertexGraph =
            p.1.partition :=
        p.1.externalComponentPartition_assembleDiagram
          (Finset.univ : Finset (Fin N)) p.2.1 p.2.2
      rw [hπ]


end Common
end SecondQuantization
