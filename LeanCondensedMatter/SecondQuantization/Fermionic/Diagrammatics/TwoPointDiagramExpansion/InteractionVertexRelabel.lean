import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for fixed-external two-point diagrams

This is the structural owner for interaction-slot relabeling. A permutation of the interaction slots
relabels standard two-point legs, the stored perfect pairing, and quartic vertex labels while fixing
the two external legs. Relabeling is packaged as an equivalence of the finite fixed-diagram type, so
full diagram sums can be reindexed without orbit/stabilizer bookkeeping. The quartic coupling
product is invariant under the same relabeling.

The convention is that `π` maps a new interaction slot to the old interaction slot whose data it
inherits. Thus the relabeled vertex sequence satisfies `q_new v = q_old (π v)`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

noncomputable section

/-- Relabel the standard two-point leg type by an interaction-slot permutation, leaving the two
external legs fixed. The permutation maps new leg identities to old leg identities. -/
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

/-- The flattened standard-leg permutation induced by an interaction-slot permutation. -/
def interactionVertexPositionRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :=
  (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).trans
    ((interactionVertexLegRelabel π).trans
      (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm)

/-- Relabel the interaction vertices of a fixed-external two-point Wick diagram. -/
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

/-- Relabeling standard two-point legs by the inverse slot permutation is the inverse leg
relabeling. -/
@[simp]
theorem interactionVertexLegRelabel_symm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    interactionVertexLegRelabel π.symm = (interactionVertexLegRelabel π).symm := by
  ext leg
  rcases leg with e | ⟨v, l⟩
  · rfl
  · rfl

/-- The flattened position relabeling induced by the inverse slot permutation is the inverse
flattened position relabeling. -/
@[simp]
theorem interactionVertexPositionRelabel_symm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    interactionVertexPositionRelabel π.symm =
      (interactionVertexPositionRelabel π).symm := by
  unfold interactionVertexPositionRelabel
  rw [interactionVertexLegRelabel_symm]
  rfl

/-- Relabeling by `π` and then by `π⁻¹` recovers the original fixed-external diagram. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_symm
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).relabelInteractionVertices π.symm = d := by
  apply Subtype.ext
  apply Common.TwoPointDiagram.ext
  · rfl
  · funext v
    change d.1.vertexLabel ⟨π (π.symm v.1), Finset.mem_univ _⟩ = d.1.vertexLabel v
    congr 1
    apply Subtype.ext
    simp
  · change (d.1.pairing.relabel (interactionVertexPositionRelabel π)).relabel
      (interactionVertexPositionRelabel π.symm) = d.1.pairing
    rw [interactionVertexPositionRelabel_symm]
    exact Pairing.relabel_symm_relabel d.1.pairing (interactionVertexPositionRelabel π)

/-- Relabeling by `π⁻¹` and then by `π` also recovers the original fixed-external diagram. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_symm_relabel
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π.symm).relabelInteractionVertices π = d := by
  simpa using d.relabelInteractionVertices_symm π.symm

/-- Interaction-vertex relabeling as an automorphism of the finite type of fixed-external diagrams. -/
noncomputable def fixedExternalTwoPointWickDiagramRelabelEquiv
    {n : ℕ} (i j : Mode) (π : Equiv.Perm (Fin n)) :
    FixedExternalTwoPointWickDiagram Mode n i j ≃
      FixedExternalTwoPointWickDiagram Mode n i j where
  toFun d := d.relabelInteractionVertices π
  invFun d := d.relabelInteractionVertices π.symm
  left_inv d := d.relabelInteractionVertices_symm π
  right_inv d := d.relabelInteractionVertices_symm_relabel π

/-- A finite sum over all fixed-external diagrams is invariant under interaction-vertex relabeling. -/
theorem sum_relabelInteractionVertices
    [Fintype Mode] {n : ℕ} (i j : Mode) (π : Equiv.Perm (Fin n))
    (F : FixedExternalTwoPointWickDiagram Mode n i j → ℂ) :
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        F (d.relabelInteractionVertices π) =
      ∑ d : FixedExternalTwoPointWickDiagram Mode n i j, F d :=
  Equiv.sum_comp (fixedExternalTwoPointWickDiagramRelabelEquiv i j π) F

/-- The product of quartic vertex weights is invariant under a permutation of interaction slots. -/
theorem orderedTwoPointVertexWeight_comp_perm
    {n : ℕ} (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (π : Equiv.Perm (Fin n)) :
    orderedTwoPointVertexWeight g (fun v => q (π v)) =
      orderedTwoPointVertexWeight g q := by
  unfold orderedTwoPointVertexWeight
  exact Equiv.prod_comp π (fun v => g (q v))

/-- Relabeling interaction vertices does not change the product of quartic coupling weights. -/
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_vertexWeight
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) (π : Equiv.Perm (Fin n)) :
    orderedTwoPointVertexWeight g
        (d.relabelInteractionVertices π).vertexLabelSequence =
      orderedTwoPointVertexWeight g d.vertexLabelSequence := by
  rw [show (d.relabelInteractionVertices π).vertexLabelSequence =
      fun v => d.vertexLabelSequence (π v) by
    funext v
    exact d.relabelInteractionVertices_vertexLabelSequence π v]
  exact orderedTwoPointVertexWeight_comp_perm g d.vertexLabelSequence π

end

end Fermionic
end SecondQuantization
