import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for fixed-external two-point diagrams

A permutation of the interaction slots induces a permutation of the standard two-point legs: the
external legs are fixed, while every interaction leg is transported together with its interaction
vertex.  This module uses that ambient leg permutation to transport both quartic vertex labels and
the stored perfect pairing of a fixed-external two-point Wick diagram.

The convention is that `π` maps a new interaction slot to the old interaction slot whose data it
inherits.  Thus the relabeled vertex sequence satisfies `q_new v = q_old (π v)`, and
`Pairing.relabel` receives the corresponding new-leg-to-old-leg permutation.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

noncomputable section

/-- Relabel the standard two-point leg type by an interaction-slot permutation, leaving the two
external legs fixed.  The permutation maps new leg identities to old leg identities. -/
def interactionVertexLegRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    OrderedTwoPointLeg n ≃ OrderedTwoPointLeg n where
  toFun
    | Sum.inl e => Sum.inl e
    | Sum.inr p => Sum.inr (⟨π p.1.1, Finset.mem_univ _⟩, p.2)
  invFun
    | Sum.inl e => Sum.inl e
    | Sum.inr p => Sum.inr (⟨π.symm p.1.1, Finset.mem_univ _⟩, p.2)
  left_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · simp
  right_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · simp

@[simp]
theorem interactionVertexLegRelabel_external {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin 2) :
    interactionVertexLegRelabel π (Sum.inl e) = (Sum.inl e : OrderedTwoPointLeg n) :=
  rfl

@[simp]
theorem interactionVertexLegRelabel_interaction {n : ℕ} (π : Equiv.Perm (Fin n))
    (v : Fin n) (l : Fin 4) :
    interactionVertexLegRelabel π
        (Sum.inr (⟨v, Finset.mem_univ v⟩, l)) =
      (Sum.inr (⟨π v, Finset.mem_univ (π v)⟩, l) : OrderedTwoPointLeg n) :=
  rfl

/-- The flattened standard-leg permutation induced by an interaction-slot permutation.  It maps
new flattened leg positions to the old flattened positions whose diagram data they inherit. -/
def interactionVertexPositionRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :=
  (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).trans
    ((interactionVertexLegRelabel π).trans
      (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm)

/-- Relabel the interaction vertices of a fixed-external two-point Wick diagram.  External labels
are unchanged, a new interaction slot `v` inherits the old label at `π v`, and the pairing is
transported by the induced standard-leg permutation. -/
def FixedExternalTwoPointWickDiagram.relabelInteractionVertices
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) : FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨{
    externalLabel := d.1.externalLabel
    vertexLabel := fun v => d.1.vertexLabel ⟨π v.1, Finset.mem_univ _⟩
    pairing := d.1.pairing.relabel (interactionVertexPositionRelabel π)
  }, d.2⟩

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_externalLabel
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).1.externalLabel = d.1.externalLabel :=
  rfl

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_vertexLabelSequence
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (d.relabelInteractionVertices π).vertexLabelSequence v = d.vertexLabelSequence (π v) :=
  rfl

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_pairing
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).1.pairing =
      d.1.pairing.relabel (interactionVertexPositionRelabel π) :=
  rfl

end

end Fermionic
end SecondQuantization
