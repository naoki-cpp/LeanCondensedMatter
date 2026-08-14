import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Diagram
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabel
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for two-point diagrams

A permutation of the interaction slots fixes the two external vertices, transports the internal
vertex labels by precomposition, and relabels the perfect pairing by the induced permutation of
flattened two-point legs. This construction is purely combinatorial and does not depend on particle
statistics or an operator realization.

The convention is that `π` maps a new interaction slot to the old slot whose data it inherits.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

noncomputable section

/-- Relabel the interaction vertices of a standard two-point diagram. The external labels are fixed,
while `π` maps each new interaction slot to the old slot whose label and paired legs it inherits. -/
def TwoPointDiagram.relabelInteractionVertices {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) :
    TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)) :=
  {
    externalLabel := d.externalLabel
    vertexLabel := fun v => d.vertexLabel ⟨π v.1, Finset.mem_univ _⟩
    pairing := d.pairing.relabel (interactionVertexPositionRelabel π)
  }

@[simp]
theorem TwoPointDiagram.relabelInteractionVertices_externalLabel {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).externalLabel = d.externalLabel :=
  rfl

@[simp]
theorem TwoPointDiagram.relabelInteractionVertices_vertexLabel {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (d.relabelInteractionVertices π).vertexLabel ⟨v, Finset.mem_univ _⟩ =
      d.vertexLabel ⟨π v, Finset.mem_univ _⟩ :=
  rfl

@[simp]
theorem TwoPointDiagram.relabelInteractionVertices_pairing {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).pairing =
      d.pairing.relabel (interactionVertexPositionRelabel π) :=
  rfl

/-- Relabeling by a permutation and then its inverse recovers the original two-point diagram. -/
@[simp]
theorem TwoPointDiagram.relabelInteractionVertices_symm {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).relabelInteractionVertices π.symm = d := by
  apply TwoPointDiagram.ext
  · rfl
  · funext v
    change d.vertexLabel ⟨π (π.symm v.1), Finset.mem_univ _⟩ = d.vertexLabel v
    congr 1
    apply Subtype.ext
    simp
  · change (d.pairing.relabel (interactionVertexPositionRelabel π)).relabel
      (interactionVertexPositionRelabel π.symm) = d.pairing
    rw [interactionVertexPositionRelabel_symm]
    exact Pairing.relabel_symm_relabel d.pairing (interactionVertexPositionRelabel π)

/-- Relabeling by the inverse permutation and then the original permutation also recovers the
original two-point diagram. -/
@[simp]
theorem TwoPointDiagram.relabelInteractionVertices_symm_relabel {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π.symm).relabelInteractionVertices π = d := by
  simpa using d.relabelInteractionVertices_symm π.symm

/-- Interaction-slot relabeling as an automorphism of standard two-point diagrams. -/
noncomputable def twoPointDiagramInteractionRelabelEquiv {n : ℕ}
    (ExternalLabel InternalLabel : Type*) (π : Equiv.Perm (Fin n)) :
    TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)) ≃
      TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)) where
  toFun d := d.relabelInteractionVertices π
  invFun d := d.relabelInteractionVertices π.symm
  left_inv d := d.relabelInteractionVertices_symm π
  right_inv d := d.relabelInteractionVertices_symm_relabel π

/-- A finite sum over all standard two-point diagrams is invariant under interaction-slot
relabeling. -/
theorem sum_relabelInteractionVertices [Fintype ExternalLabel] [Fintype InternalLabel]
    {R : Type*} [AddCommMonoid R] {n : ℕ} (π : Equiv.Perm (Fin n))
    (F : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)) → R) :
    ∑ d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)),
        F (d.relabelInteractionVertices π) =
      ∑ d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)), F d :=
  Equiv.sum_comp (twoPointDiagramInteractionRelabelEquiv ExternalLabel InternalLabel π) F

end

end Common
end SecondQuantization
