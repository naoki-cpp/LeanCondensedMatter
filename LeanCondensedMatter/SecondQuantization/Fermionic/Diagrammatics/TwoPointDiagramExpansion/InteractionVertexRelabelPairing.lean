import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelMixedPosition

set_option linter.style.header false

/-!
# Mixed-order pairing covariance under interaction-vertex relabeling

Away from interaction-time diagonals, `InteractionVertexRelabelMixedPosition` identifies the induced
mixed-position permutation with the identity.  This file converts that statement into covariance of
the standard-to-mixed position equivalence and of the pairing stored in mixed atomic order.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

noncomputable section

/-- Standard-position relabeling followed by conversion to the old mixed order agrees with first
converting to the new mixed order and then applying the induced mixed-position relabeling. -/
theorem standardToMixedAtomicPositionEquiv_relabelInteractionVertices {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (standardToMixedAtomicPositionEquiv τ τ' σ).trans
        (interactionVertexMixedPositionRelabel π τ τ' σ) =
      (interactionVertexPositionRelabel π).trans
        (standardToMixedAtomicPositionEquiv τ τ' (fun v => σ (π.symm v))) := by
  apply Equiv.ext
  intro p
  simp [standardToMixedAtomicPositionEquiv, interactionVertexMixedPositionRelabel,
    interactionVertexPositionRelabel]

/-- For injective interaction times, standard-to-mixed conversion is exactly equivariant under the
interaction-slot relabeling. -/
theorem standardToMixedAtomicPositionEquiv_relabelInteractionVertices_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (interactionVertexPositionRelabel π).trans
        (standardToMixedAtomicPositionEquiv τ τ' (fun v => σ (π.symm v))) =
      standardToMixedAtomicPositionEquiv τ τ' σ := by
  rw [← standardToMixedAtomicPositionEquiv_relabelInteractionVertices π τ τ' σ]
  rw [interactionVertexMixedPositionRelabel_eq_refl_of_injective π τ τ' σ hσ]
  simp

/-- The inverse standard-to-mixed equivalence absorbs the standard interaction-slot relabeling on
injective interaction-time assignments. -/
theorem standardToMixedAtomicPositionEquiv_symm_trans_relabel_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (standardToMixedAtomicPositionEquiv τ τ' σ).symm.trans
        (interactionVertexPositionRelabel π) =
      (standardToMixedAtomicPositionEquiv τ τ' (fun v => σ (π.symm v))).symm := by
  have h := standardToMixedAtomicPositionEquiv_relabelInteractionVertices_of_injective
    π τ τ' σ hσ
  apply Equiv.ext
  intro p
  have hp := congrArg (fun e => e.symm p) h
  simpa using hp

/-- On injective interaction-time assignments, relabeling the interaction vertices and
inverse-precomposing the old time assignment leave the pairing in mixed atomic order unchanged. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).pairingInMixedOrder τ τ' σ =
      d.pairingInMixedOrder τ τ' (fun v => σ (π.symm v)) := by
  apply Pairing.ext
  intro p
  simp [FixedExternalTwoPointWickDiagram.pairingInMixedOrder,
    orderedTwoPointPairingCastEquiv, Pairing.relabel_partner,
    standardToMixedAtomicPositionEquiv,
    FixedExternalTwoPointWickDiagram.relabelInteractionVertices,
    interactionVertexPositionRelabel,
    interactionVertexMixedPositionRelabel_apply_eq_of_injective π τ τ' σ hσ]

end

end Fermionic
end SecondQuantization
