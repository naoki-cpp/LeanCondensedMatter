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
  partition : Finpartition (Finset.univ : Finset (Fin (2 * E)))
  evenBlocks : ∀ B : partition.parts, Even (B : Finset (Fin (2 * E))).card
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

end Common
end SecondQuantization
