import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabel
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for fixed-external two-point diagrams

`SecondQuantization.Common` owns the statistics-independent interaction-slot relabeling of standard
two-point legs and flattened positions. This module lifts that relabeling to the fermionic
fixed-external Wick-diagram type, transports quartic labels and pairings, and proves invariance of
the quartic coupling product.

The convention is that `π` maps a new interaction slot to the old interaction slot whose data it
inherits. Thus the relabeled vertex sequence satisfies `q_new v = q_old (π v)`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

noncomputable section

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
