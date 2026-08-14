import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPieceField

set_option linter.style.header false

/-!
# The external component's mixed pairs as pairs of the standalone piece

Common owns mixed component positions, pairs, endpoint transport, crossing counts, and the standalone
external-piece position embedding. This module identifies the external component of a fermionic
fixed-external diagram with the pairing of its standalone external piece and then transports the
physical contraction product.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
theorem FixedExternalTwoPointWickDiagram.externalPiece_partner_externalPieceMixedPositionEquiv_symm
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pos : d.1.MixedComponentPosition τ τ' σ d.1.externalComponentPart) :
    (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).partner
        ((d.1.externalPieceMixedPositionEquiv τ τ' σ).symm pos) =
      (d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
        (d.1.mixedRestrictedPartner τ τ' σ d.1.externalComponentPart pos) := by
  apply (d.1.externalPieceMixedPositionEquiv τ τ' σ).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [Common.TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
    d.1.mixedRestrictedPartner_val]
  change d.1.externalPieceMixedPosition τ τ' σ
      ((d.1.externalPiece.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).partner
        ((d.1.externalPieceMixedPositionEquiv τ τ' σ).symm pos)) =
    (d.1.pairingInMixedOrder τ τ' σ).partner (pos : Fin (2 * (2 * n + 1)))
  rw [← d.1.externalPieceMixedPosition_partner,
    ← Common.TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
    Equiv.apply_symm_apply]

/-- The external component's mixed pairs are the normalized pairs of the standalone piece. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceComponentPairEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart ≃
      (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).NormalizedPair :=
  d.1.mixedComponentPairRestrictedEquiv τ τ' σ d.1.externalComponentPart
    (d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ))
    (d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ)

omit [LinearOrder Mode] [Fintype Mode] in
theorem FixedExternalTwoPointWickDiagram.externalPieceComponentPairEquiv_pair_eq_or_swap
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart) :
    (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.1.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 0)),
          (d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.1.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 1))) ∨
      (d.externalPieceComponentPairEquiv τ τ' σ pr).1 =
        ((d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.1.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 1)),
          (d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
            (d.1.mixedComponentPairEndpointEquiv τ τ' σ d.1.externalComponentPart (pr, 0))) :=
  d.1.mixedComponentPairRestrictedEquiv_pair_eq_or_swap τ τ' σ d.1.externalComponentPart
    (d.1.externalPieceMixedPositionEquiv τ τ' σ).symm
    (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ))
    (d.externalPiece_partner_externalPieceMixedPositionEquiv_symm τ τ' σ) pr

omit [LinearOrder Mode] [Fintype Mode] in
theorem FixedExternalTwoPointWickDiagram.externalPieceMixedPosition_externalPieceComponentPairEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart) :
    (d.1.externalPieceMixedPosition τ τ' σ (d.externalPieceComponentPairEquiv τ τ' σ pr).1.1,
        d.1.externalPieceMixedPosition τ τ' σ
          (d.externalPieceComponentPairEquiv τ τ' σ pr).1.2) = pr.1.1 := by
  have hf : ∀ x : d.1.MixedComponentPosition τ τ' σ d.1.externalComponentPart,
      d.1.externalPieceMixedPosition τ τ' σ
          ((d.1.externalPieceMixedPositionEquiv τ τ' σ).symm x) =
        (x : Fin (2 * (2 * n + 1))) := by
    intro x
    rw [← Common.TwoPointDiagram.externalPieceMixedPositionEquiv_apply,
      Equiv.apply_symm_apply]
  rcases d.externalPieceComponentPairEquiv_pair_eq_or_swap τ τ' σ pr with h | h
  · rw [h]
    simp [hf]
  · exfalso
    have hnorm :
        (d.externalPieceComponentPairEquiv τ τ' σ pr).1.1 <
          (d.externalPieceComponentPairEquiv τ τ' σ pr).1.2 :=
      (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs_normalized
        (d.externalPieceComponentPairEquiv τ τ' σ pr).2
    have hmono := d.1.externalPieceMixedPosition_strictMono τ τ' σ hnorm
    rw [h] at hmono
    simp only [hf, Common.TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_zero,
      Common.TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_one] at hmono
    exact absurd ((d.1.pairingInMixedOrder τ τ' σ).pairs_normalized pr.1.2) (asymm hmono)

omit [LinearOrder Mode] [Fintype Mode] in
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount_externalComponentPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.1.mixedComponentCrossingCount τ τ' σ d.1.externalComponentPart =
      (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).crossingCount := by
  classical
  rw [Common.TwoPointDiagram.mixedComponentCrossingCount,
    Common.TwoPointDiagram.mixedComponentOrientedCrossingCount,
    Pairing.componentCrossingCount, Pairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp (Equiv.prodCongr (d.externalPieceComponentPairEquiv τ τ' σ)
      (d.externalPieceComponentPairEquiv τ τ' σ))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff :
      Crosses
          (d.1.mixedComponentPairSigmaEquiv τ τ' σ ⟨d.1.externalComponentPart, x.1⟩).1
          (d.1.mixedComponentPairSigmaEquiv τ τ' σ ⟨d.1.externalComponentPart, x.2⟩).1 ↔
        Crosses (d.externalPieceComponentPairEquiv τ τ' σ x.1).1
          (d.externalPieceComponentPairEquiv τ τ' σ x.2).1 := by
    rw [Common.TwoPointDiagram.mixedComponentPairSigmaEquiv_apply,
      Common.TwoPointDiagram.mixedComponentPairSigmaEquiv_apply,
      ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x.1,
      ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x.2]
    exact crosses_map_iff (d.1.externalPieceMixedPosition τ τ' σ)
      (d.1.externalPieceMixedPosition_strictMono τ τ' σ) _ _ _ _
  exact if_congr hiff rfl rfl

/-- The external component's mixed value is the value of the standalone piece. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_externalComponentPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ)
    (σ : Fin n → ℝ) :
    d.mixedComponentPairingValue ε β τ τ' σ d.1.externalComponentPart =
      orderedTwoPointPairingValue ε β i j τ τ' (d.1.externalPieceTimes σ)
        d.externalPiece.vertexLabelSequence
        (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)) := by
  classical
  have hpair : ∀ x : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
      mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
          d.externalPiece.vertexLabelSequence
          (d.externalPieceComponentPairEquiv τ τ' σ x).1.1
          (d.externalPieceComponentPairEquiv τ τ' σ x).1.2 =
        d.mixedPairContractionValue ε β τ τ' σ x.1 := by
    intro x
    have hpos := d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x
    have hfirst : d.1.externalPieceMixedPosition τ τ' σ
        (d.externalPieceComponentPairEquiv τ τ' σ x).1.1 = x.1.1.1 :=
      congrArg Prod.fst hpos
    have hsecond : d.1.externalPieceMixedPosition τ τ' σ
        (d.externalPieceComponentPairEquiv τ τ' σ x).1.2 = x.1.1.2 :=
      congrArg Prod.snd hpos
    rw [← d.mixedTimeOrderedAtomicPairValue_externalPieceMixedPosition ε β τ τ' σ,
      FixedExternalTwoPointWickDiagram.mixedPairContractionValue, hfirst, hsecond]
  have hprod :
      (∏ pr ∈ (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2) =
        ∏ pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
          d.mixedPairContractionValue ε β τ τ' σ pr.1 := by
    calc
      (∏ pr ∈ (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2) =
          ∏ pr : (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).NormalizedPair,
            mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
              d.externalPiece.vertexLabelSequence pr.1.1 pr.1.2 :=
        Finset.prod_subtype
          (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs
          (fun _ => Iff.rfl)
          (fun pr => mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2)
      _ = ∏ x : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
            mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
              d.externalPiece.vertexLabelSequence
              (d.externalPieceComponentPairEquiv τ τ' σ x).1.1
              (d.externalPieceComponentPairEquiv τ τ' σ x).1.2 :=
        (Equiv.prod_comp (d.externalPieceComponentPairEquiv τ τ' σ)
          (fun pr => mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1.1 pr.1.2)).symm
      _ = ∏ pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
            d.mixedPairContractionValue ε β τ τ' σ pr.1 :=
        Finset.prod_congr rfl fun x _ => hpair x
  have hweight :
      d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ d.1.externalComponentPart =
        (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).weight
          Common.Statistics.fermion := by
    rw [Common.TwoPointDiagram.mixedComponentWeight,
      d.mixedComponentCrossingCount_externalComponentPart]
    rfl
  rw [FixedExternalTwoPointWickDiagram.mixedComponentPairingValue, hweight, ← hprod]
  rfl

end Fermionic
end SecondQuantization
