import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for fixed-external two-point diagrams

`SecondQuantization.Common` owns the statistics-independent relabeling of a complete two-point
diagram. This module only lifts that operation through the fixed fermionic external-label subtype
and records invariance of the quartic coupling product.

The convention is that `π` maps a new interaction slot to the old interaction slot whose data it
inherits. Thus the relabeled vertex sequence satisfies `q_new v = q_old (π v)`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

noncomputable section

/-- Lift Common interaction-vertex relabeling to a two-point Wick diagram with fixed external
annihilation/creation labels. -/
def FixedExternalTwoPointWickDiagram.relabelInteractionVertices
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) : FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨d.1.relabelInteractionVertices π, by
    simpa using d.2⟩

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_externalLabel
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).1.externalLabel = d.1.externalLabel :=
  Common.TwoPointDiagram.relabelInteractionVertices_externalLabel d.1 π

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
  Common.TwoPointDiagram.relabelInteractionVertices_pairing d.1 π

/-- Relabeling by `π` and then by `π⁻¹` recovers the original fixed-external diagram. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_symm
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).relabelInteractionVertices π.symm = d := by
  apply Subtype.ext
  exact d.1.relabelInteractionVertices_symm π

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
  unfold orderedTwoPointVertexWeight
  exact Equiv.prod_comp π (fun v => g (d.vertexLabelSequence v))

end

end Fermionic
end SecondQuantization
