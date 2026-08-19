import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalPiece
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
        (d.mixedRestrictedPartner τ τ' σ d.externalComponentPart pos) := by
  apply (d.externalPieceMixedPositionEquiv τ τ' σ).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
    d.mixedRestrictedPartner_val]
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
  d.mixedComponentPairRestrictedEquiv τ τ' σ d.externalComponentPart
    (d.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
    (d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ)

/-- Before using normalized order, the external-piece pair equivalence transports the two ambient
component endpoints either in their original order or swapped. -/
theorem TwoPointDiagram.externalPieceComponentPairEquiv_pair_eq_or_swap
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.externalComponentPart) :
    (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 0)),
          (d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 1))) ∨
      (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 1)),
          (d.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 0))) :=
  d.mixedComponentPairRestrictedEquiv_pair_eq_or_swap τ τ' σ d.externalComponentPart
    (d.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
    (d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ) pr

/-- Mapping the normalized standalone external-piece pair back to ambient mixed positions recovers
the normalized ambient component pair endpoints in their original order. -/
theorem TwoPointDiagram.externalPieceMixedPosition_externalPieceComponentPairEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.externalComponentPart) :
    (d.externalPieceMixedPosition τ τ' σ (d.externalPieceComponentPairEquiv τ τ' σ pr).1.1,
        d.externalPieceMixedPosition τ τ' σ
          (d.externalPieceComponentPairEquiv τ τ' σ pr).1.2) = pr.1.1 := by
  have hf : ∀ x : d.MixedComponentPosition τ τ' σ d.externalComponentPart,
      d.externalPieceMixedPosition τ τ' σ
          ((d.externalPieceMixedPositionEquiv τ τ' σ).symm x) =
        (x : Fin (2 * (2 * n + 1))) := by
    intro x
    rw [← TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
      Equiv.apply_symm_apply]
  rcases d.externalPieceComponentPairEquiv_pair_eq_or_swap τ τ' σ pr with h | h
  · rw [h]
    simp [hf]
  · exfalso
    have hnorm :
        (d.externalPieceComponentPairEquiv τ τ' σ pr).1.1 <
          (d.externalPieceComponentPairEquiv τ τ' σ pr).1.2 :=
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).pairs_normalized
        (d.externalPieceComponentPairEquiv τ τ' σ pr).2
    have hmono := d.externalPieceMixedPosition_strictMono τ τ' σ hnorm
    rw [h] at hmono
    simp only [hf, TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_zero,
      TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_one] at hmono
    exact absurd ((d.pairingInMixedOrder τ τ' σ).pairs_normalized pr.1.2) (asymm hmono)

/-- The crossing count internal to the ambient external component equals the crossing count of the
standalone external-piece pairing. -/
theorem TwoPointDiagram.mixedComponentCrossingCount_externalComponentPart
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedComponentCrossingCount τ τ' σ d.externalComponentPart =
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).crossingCount := by
  classical
  rw [TwoPointDiagram.mixedComponentCrossingCount,
    TwoPointDiagram.mixedComponentOrientedCrossingCount,
    Pairing.componentCrossingCount, Pairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp (Equiv.prodCongr (d.externalPieceComponentPairEquiv τ τ' σ)
      (d.externalPieceComponentPairEquiv τ τ' σ))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff :
      Crosses
          (d.mixedComponentPairSigmaEquiv τ τ' σ ⟨d.externalComponentPart, x.1⟩).1
          (d.mixedComponentPairSigmaEquiv τ τ' σ ⟨d.externalComponentPart, x.2⟩).1 ↔
        Crosses (d.externalPieceComponentPairEquiv τ τ' σ x.1).1
          (d.externalPieceComponentPairEquiv τ τ' σ x.2).1 := by
    rw [TwoPointDiagram.mixedComponentPairSigmaEquiv_apply,
      TwoPointDiagram.mixedComponentPairSigmaEquiv_apply,
      ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x.1,
      ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x.2]
    exact crosses_map_iff (d.externalPieceMixedPosition τ τ' σ)
      (d.externalPieceMixedPosition_strictMono τ τ' σ) _ _ _ _
  exact if_congr hiff rfl rfl

end Common
end SecondQuantization
