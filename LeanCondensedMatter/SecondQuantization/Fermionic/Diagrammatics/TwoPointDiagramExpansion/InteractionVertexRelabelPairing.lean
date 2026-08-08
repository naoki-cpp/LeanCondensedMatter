import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelMixedPosition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPositionLeg

set_option linter.style.header false

/-!
# Mixed-order pairing covariance under interaction-vertex relabeling

Away from interaction-time diagonals, interaction-slot relabeling does not move mixed atomic
positions. This file transports that position identity back to the standard diagram enumeration and
uses it to prove exact covariance of the diagram pairing in mixed-time order.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- Reading a standard leg after applying the flattened interaction-slot relabeling is the same as
relabeling the standard leg itself. -/
@[simp]
theorem twoPointLegEquiv_interactionVertexPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n))
    (p : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (interactionVertexPositionRelabel π p) =
      interactionVertexLegRelabel π
        (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) p) := by
  change
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
          (interactionVertexLegRelabel π
            (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) p))) =
      interactionVertexLegRelabel π
        (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) p)
  exact (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).apply_symm_apply _

/-- For injective interaction times, transporting a mixed position back to the standard diagram
enumeration commutes exactly with interaction-slot relabeling. -/
theorem interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p : Fin (2 * (2 * n + 1))) :
    interactionVertexPositionRelabel π (mixedTimeAmbientPositionEquiv τ τ' σ p) =
      mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v)) p := by
  apply (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
  rw [twoPointLegEquiv_interactionVertexPositionRelabel,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  have h := mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel
    π τ τ' σ p
  rw [interactionVertexMixedPositionRelabel_apply_eq_of_injective π τ τ' σ hσ p] at h
  exact h.symm

/-- Under injective interaction times, relabeling the interaction vertices and evaluating the
pairing in the new mixed order is exactly the original mixed-order pairing at the inverse-precomposed
time assignment. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
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
        ((d.relabelInteractionVertices π).1.pairing.partner
          (mixedTimeAmbientPositionEquiv τ τ' σ p)) := by
        rw [(d.relabelInteractionVertices π).mixedTimeAmbientPositionEquiv_partner]
    _ = d.1.pairing.partner
        (interactionVertexPositionRelabel π
          (mixedTimeAmbientPositionEquiv τ τ' σ p)) := by
        rw [FixedExternalTwoPointWickDiagram.relabelInteractionVertices_pairing,
          Pairing.relabel_partner]
        exact (interactionVertexPositionRelabel π).apply_symm_apply _
    _ = d.1.pairing.partner
        (mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v)) p) := by
        rw [interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective
          π τ τ' σ hσ p]
    _ = mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))
        ((d.pairingInMixedOrder τ τ' (fun v => σ (π.symm v))).partner p) := by
        symm
        exact d.mixedTimeAmbientPositionEquiv_partner
          τ τ' (fun v => σ (π.symm v)) p

end Fermionic
end SecondQuantization
