import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossing

set_option linter.style.header false

/-!
# Pairing of the standalone external component

The canonical external component of a standard two-point diagram can be standardized to its own
consecutive interaction slots.  This module identifies the normalized mixed pairs of that standalone
piece with the mixed-pair fiber of the ambient external component and transports pair endpoints and
crossing counts across the identification.

Everything here is statistics-independent and depends only on the Common two-point pairing,
component decomposition, and external-piece mixed-position embedding.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- The standalone external-piece pairing partner is natural under the inverse mixed-position
identification with the ambient external component. -/
theorem TwoPointDiagram.externalPiece_partner_externalPieceMixedPositionEquiv_symm
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pos : d.MixedComponentPosition τ τ' σ d.externalComponentPart) :
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).partner
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm pos) =
      (d.externalPieceMixedPositionEquiv τ τ' σ).symm
        (((d.pairingInMixedOrder τ τ' σ).restrict
          (fun p => d.mixedPositionComponent τ τ' σ p = d.externalComponentPart)
          (fun p => by rw [d.mixedPositionComponent_partner])).partner pos) := by
  apply (d.externalPieceMixedPositionEquiv τ τ' σ).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
    PairingOn.restrict_partner_val]
  rw [← d.externalPieceMixedPosition_partner,
    ← TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
    Equiv.apply_symm_apply]

/-- The mixed pairs internal to the ambient external component are canonically the normalized pairs
of the standalone external piece. -/
noncomputable def TwoPointDiagram.externalPieceComponentPairEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.MixedComponentPair τ τ' σ d.externalComponentPart ≃
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).NormalizedPair :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEquivOfEndpointEquiv
    (fun p => d.mixedPositionComponent τ τ' σ p = d.externalComponentPart)
    (fun p => by rw [d.mixedPositionComponent_partner])
    (d.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
    (fun pos => d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ pos)

/-- Mapping the normalized standalone external-piece pair back to ambient mixed positions recovers
the normalized ambient component pair endpoints in their original order. -/
theorem TwoPointDiagram.externalPieceMixedPosition_externalPieceComponentPairEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.externalComponentPart) :
    (d.externalPieceMixedPosition τ τ' σ (d.externalPieceComponentPairEquiv τ τ' σ pr).1.1,
        d.externalPieceMixedPosition τ τ' σ
          (d.externalPieceComponentPairEquiv τ τ' σ pr).1.2) = pr.1.1 := by
  have hf (x : d.MixedComponentPosition τ τ' σ d.externalComponentPart) :
      d.externalPieceMixedPosition τ τ' σ
          ((d.externalPieceMixedPositionEquiv τ τ' σ).symm x) =
        (x : Fin (2 * (2 * n + 1))) := by
    rw [← TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
      Equiv.apply_symm_apply]
  have horder :
      (d.externalPieceMixedPositionEquiv τ τ' σ).symm
          (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 0)) <
        (d.externalPieceMixedPositionEquiv τ τ' σ).symm
          (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 1)) := by
    by_contra h
    have hmono := (d.externalPieceMixedPosition_strictMono τ τ' σ).monotone
      (le_of_not_gt h)
    simp only [hf, d.mixedComponentPairEndpointEquiv_apply_val,
      Pairing.pairEndpoint_one, Pairing.pairEndpoint_zero] at hmono
    exact (not_le_of_gt ((d.pairingInMixedOrder τ τ' σ).pairs_normalized pr.1.2)) hmono
  have hpair :
      (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 0)),
          (d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 1))) := by
    change
      ((d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).normalizedPairOfEndpointEquiv
        (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart)
        (d.externalPieceMixedPositionEquiv τ τ' σ).symm pr).1 = _
    apply Pairing.normalizedPairOfEndpointEquiv_pair_eq_of_lt
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
    · intro q
      rw [d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ]
      apply congrArg (d.externalPieceMixedPositionEquiv τ τ' σ).symm
      apply Subtype.ext
      simp only [PairingOn.restrict_partner_val,
        d.mixedComponentPairEndpointEquiv_apply_val,
        Pairing.pairEndpoint_zero, Pairing.pairEndpoint_one]
      exact (((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff
        q.1.1.1 q.1.1.2).1 q.1.2).2
    · exact horder
  rw [hpair]
  simp only [hf, d.mixedComponentPairEndpointEquiv_apply_val,
    Pairing.pairEndpoint_zero, Pairing.pairEndpoint_one]

/-- The crossing count internal to the ambient external component equals the crossing count of the
standalone external-piece pairing. -/
theorem TwoPointDiagram.mixedComponentCrossingCount_externalComponentPart
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedComponentCrossingCount τ τ' σ d.externalComponentPart =
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).crossingCount := by
  classical
  rw [TwoPointDiagram.mixedComponentCrossingCount,
    Pairing.componentCrossingCount, Fintype.sum_prod_type,
    Pairing.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv
    (fun p : d.MixedComponentPair τ τ' σ d.externalComponentPart => p.1.1)
    (fun p : (d.externalPiece.pairingInMixedOrder τ τ'
      (d.externalPieceTimes σ)).NormalizedPair => p.1)
    (d.externalPieceComponentPairEquiv τ τ' σ)
    (fun p q => by
      rw [← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ p,
        ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ q]
      exact crosses_map_iff (d.externalPieceMixedPosition τ τ' σ)
        (d.externalPieceMixedPosition_strictMono τ τ' σ) _ _ _ _)

end Common
end SecondQuantization
