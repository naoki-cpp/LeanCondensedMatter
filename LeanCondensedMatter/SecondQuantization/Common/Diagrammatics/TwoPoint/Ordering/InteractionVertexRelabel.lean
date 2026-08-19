import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabel
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabelMixedPosition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for two-point diagrams

A permutation of the interaction slots fixes the two external vertices, transports the internal
vertex labels by precomposition, and relabels the perfect pairing by the induced permutation of
flattened two-point legs. The same construction is compatible with the mixed imaginary-time pairing
away from interaction-time diagonals. Everything here is purely combinatorial and does not depend on
particle statistics or an operator realization.

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

/-- Flattening an interaction-relabelled standard position agrees with relabeling the corresponding
ordered two-point leg. -/
private theorem twoPointLegEquiv_interactionVertexPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n))
    (p : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :
    twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (interactionVertexPositionRelabel π p) =
      interactionVertexLegRelabel π
        (twoPointLegEquiv (Finset.univ : Finset (Fin n)) p) := by
  change
    twoPointLegEquiv (Finset.univ : Finset (Fin n))
        ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
          (interactionVertexLegRelabel π
            (twoPointLegEquiv (Finset.univ : Finset (Fin n)) p))) =
      interactionVertexLegRelabel π
        (twoPointLegEquiv (Finset.univ : Finset (Fin n)) p)
  exact (twoPointLegEquiv (Finset.univ : Finset (Fin n))).apply_symm_apply _

/-- At injective interaction times, interaction-slot relabeling commutes with the mixed-order ambient
position equivalence. -/
private theorem interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p : Fin (2 * (2 * n + 1))) :
    interactionVertexPositionRelabel π (mixedTimeAmbientPositionEquiv τ τ' σ p) =
      mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v)) p := by
  apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
  rw [twoPointLegEquiv_interactionVertexPositionRelabel,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  have h := mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel
    π τ τ' σ p
  rw [interactionVertexMixedPositionRelabel_apply_eq_of_injective π τ τ' σ hσ p] at h
  exact h.symm

/-- Under injective interaction times, interaction-vertex relabeling commutes with the Common
mixed-order pairing. -/
theorem TwoPointDiagram.pairingInMixedOrder_relabelInteractionVertices_of_injective
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).pairingInMixedOrder τ τ' σ =
      d.pairingInMixedOrder τ τ' (fun v => σ (π.symm v)) := by
  apply Pairing.ext
  apply Equiv.ext
  intro p
  apply (mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))).injective
  calc
    mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))
        (((d.relabelInteractionVertices π).pairingInMixedOrder τ τ' σ).partner p) =
      interactionVertexPositionRelabel π
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (((d.relabelInteractionVertices π).pairingInMixedOrder τ τ' σ).partner p)) := by
        symm
        exact interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective
          π τ τ' σ hσ _
    _ = interactionVertexPositionRelabel π
        ((d.relabelInteractionVertices π).pairing.partner
          (mixedTimeAmbientPositionEquiv τ τ' σ p)) := by
        rw [(d.relabelInteractionVertices π).mixedTimeAmbientPositionEquiv_partner]
    _ = d.pairing.partner
        (interactionVertexPositionRelabel π
          (mixedTimeAmbientPositionEquiv τ τ' σ p)) := by
        rw [d.relabelInteractionVertices_pairing, Pairing.relabel_partner]
        exact (interactionVertexPositionRelabel π).apply_symm_apply _
    _ = d.pairing.partner
        (mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v)) p) := by
        rw [interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective
          π τ τ' σ hσ p]
    _ = mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))
        ((d.pairingInMixedOrder τ τ' (fun v => σ (π.symm v))).partner p) := by
        symm
        exact d.mixedTimeAmbientPositionEquiv_partner
          τ τ' (fun v => σ (π.symm v)) p

end

end Common
end SecondQuantization
