import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairEquiv

set_option linter.style.header false

/-!
# The external component's mixed pairs as pairs of the standalone piece

The mixed pairs of the external component were already identified with the normalized pairs of
`restrictedExternalPairing`, the pairing the ambient diagram carries on that component's legs. What
the linked-cluster factorization needs instead is the pairing of the **piece as a diagram in its own
right**, in the mixed order the piece computes from the times it inherits — that is the pairing a
perturbative coefficient is summed over.

`ExternalPiece` supplies both halves of the identification: the piece's mixed positions are exactly
the component's mixed positions, and the embedding intertwines the two mixed-order partners. Feeding
them to the generic restriction machinery of `MixedComponentPairEquiv` gives the pair equivalence,
and with it the description of each transported pair as the endpoint pair or its swap.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The piece's mixed pairing, read on the component's mixed positions, is the ambient restricted
partner. -/
theorem FixedExternalTwoPointWickDiagram.externalPiece_partner_externalPieceMixedPositionEquiv_symm
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pos : d.MixedComponentPosition τ τ' σ d.1.externalComponentPart) :
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).partner
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm pos) =
      (d.externalPieceMixedPositionEquiv τ τ' σ).symm
        (d.mixedRestrictedPartner τ τ' σ d.1.externalComponentPart pos) := by
  apply (d.externalPieceMixedPositionEquiv τ τ' σ).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [FixedExternalTwoPointWickDiagram.externalPieceMixedPositionEquiv_apply,
    d.mixedRestrictedPartner_val, ← d.externalPieceMixedPosition_partner,
    ← FixedExternalTwoPointWickDiagram.externalPieceMixedPositionEquiv_apply,
    Equiv.apply_symm_apply]

/-- **The external component's mixed pairs are the normalized pairs of the standalone piece**, in
the mixed order the piece computes from the times it inherits. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceComponentPairEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.MixedComponentPair τ τ' σ d.1.externalComponentPart ≃
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).NormalizedPair :=
  d.mixedComponentPairRestrictedEquiv τ τ' σ d.1.externalComponentPart
    (d.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
    (d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ)

omit [LinearOrder Mode] [Fintype Mode] in
/-- Transporting a mixed pair to the piece preserves its endpoints up to their normalized order. -/
theorem FixedExternalTwoPointWickDiagram.externalPieceComponentPairEquiv_pair_eq_or_swap
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart) :
    (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 0)),
          (d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 1))) ∨
      (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 1)),
          (d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 0))) :=
  d.mixedComponentPairRestrictedEquiv_pair_eq_or_swap τ τ' σ d.1.externalComponentPart
    (d.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
    (d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ) pr

end Fermionic
end SecondQuantization
