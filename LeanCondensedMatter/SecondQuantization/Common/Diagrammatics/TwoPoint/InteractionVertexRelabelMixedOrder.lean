import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.InteractionVertexRelabel
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabelMixedPosition

set_option linter.style.header false

/-!
# Mixed-order pairing covariance under interaction-slot relabeling

Interaction-slot relabeling acts on standard two-point legs, flattened positions, and pairings without
reference to particle statistics or an operator realization. Away from interaction-time diagonals,
the induced mixed-position permutation is the identity, so relabeling the diagram is equivalent to
precomposing the interaction-time assignment by the inverse slot permutation.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Flattening an interaction-relabelled standard position agrees with relabeling the corresponding
ordered two-point leg. -/
theorem twoPointLegEquiv_interactionVertexPositionRelabel {n : ℕ}
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
theorem interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective {n : ℕ}
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

end Common
end SecondQuantization
