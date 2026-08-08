import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling equivalence

Interaction-slot relabeling is invertible.  This file packages the inverse relabeling explicitly and
exposes the finite-sum reindexing theorem needed to avoid orbit/stabilizer bookkeeping in the
component-shuffle bridge.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

noncomputable section

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

end

end Fermionic
end SecondQuantization
