import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPieceField

set_option linter.style.header false

/-!
# The external component's mixed pairs as pairs of the standalone piece

The mixed pairs of the external component are identified structurally through the canonical external
slot split, whose left pairing is `externalVacuumSplit.1.pairing`. The linked-cluster factorization
then relates those ambient component pairs to the pairing of the **piece as a diagram in its own
right**, in the mixed order the piece computes from the times it inherits — that is the pairing a
perturbative coefficient is summed over.

`ExternalPiece` supplies both halves of the identification: the piece's mixed positions are exactly
the component's mixed positions, and the embedding intertwines the two mixed-order partners. Feeding
them to the generic component-pair transport machinery of `MixedComponentPairEquiv` gives the pair
equivalence, and with it the description of each transported pair as the endpoint pair or its swap.

The swap never occurs: the embedding of positions is strictly monotone, so a transported pair keeps
its normalized order. That makes `Crosses` — a purely order-theoretic relation — transport along the
pair equivalence, and the component's mixed crossing count is the piece's own crossing count.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The piece's mixed pairing, read on the component's mixed positions, is the ambient component-local
partner. -/
theorem FixedExternalTwoPointWickDiagram.externalPiece_partner_externalPieceMixedPositionEquiv_symm
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pos : d.1.MixedComponentPosition τ τ' σ d.1.externalComponentPart) :
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

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The ambient pair is the piece's pair, embedded.** The endpoints keep their normalized order:
the embedding is strictly monotone, so the swapped alternative would reverse it. -/
theorem FixedExternalTwoPointWickDiagram.externalPieceMixedPosition_externalPieceComponentPairEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart) :
    (d.externalPieceMixedPosition τ τ' σ (d.externalPieceComponentPairEquiv τ τ' σ pr).1.1,
        d.externalPieceMixedPosition τ τ' σ
          (d.externalPieceComponentPairEquiv τ τ' σ pr).1.2) =
      pr.1.1 := by
  have hf : ∀ x : d.1.MixedComponentPosition τ τ' σ d.1.externalComponentPart,
      d.externalPieceMixedPosition τ τ' σ
          ((d.externalPieceMixedPositionEquiv τ τ' σ).symm x) =
        (x : Fin (2 * (2 * n + 1))) := by
    intro x
    rw [← FixedExternalTwoPointWickDiagram.externalPieceMixedPositionEquiv_apply,
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
    simp only [hf, FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointEquiv_apply_zero,
      FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointEquiv_apply_one] at hmono
    exact absurd ((d.pairingInMixedOrder τ τ' σ).pairs_normalized pr.1.2) (asymm hmono)

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The external component's mixed crossings are the crossings of the standalone piece.**
`Crosses` is purely order-theoretic and the piece's mixed positions sit inside the ambient ones
order-preservingly, so the crossing count transports along the pair equivalence. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount_externalComponentPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedComponentCrossingCount τ τ' σ d.1.externalComponentPart =
      (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).crossingCount := by
  classical
  rw [FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount,
    FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount,
    Pairing.componentCrossingCount, Pairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp (Equiv.prodCongr (d.externalPieceComponentPairEquiv τ τ' σ)
      (d.externalPieceComponentPairEquiv τ τ' σ))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff :
      Crosses
          (d.mixedComponentPairSigmaEquiv τ τ' σ ⟨d.1.externalComponentPart, x.1⟩).1
          (d.mixedComponentPairSigmaEquiv τ τ' σ ⟨d.1.externalComponentPart, x.2⟩).1 ↔
        Crosses (d.externalPieceComponentPairEquiv τ τ' σ x.1).1
          (d.externalPieceComponentPairEquiv τ τ' σ x.2).1 := by
    rw [FixedExternalTwoPointWickDiagram.mixedComponentPairSigmaEquiv_apply,
      FixedExternalTwoPointWickDiagram.mixedComponentPairSigmaEquiv_apply,
      ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x.1,
      ← d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x.2]
    exact crosses_map_iff (d.externalPieceMixedPosition τ τ' σ)
      (d.externalPieceMixedPosition_strictMono τ τ' σ) _ _ _ _
  exact if_congr hiff rfl rfl

/-- **The external component's mixed value is the value of the standalone piece.** Its weight is the
piece's weight because the crossing counts agree, and its contraction product is the piece's because
each pair of the component is a pair of the piece, contracted at the times the piece inherits. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_externalComponentPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ)
    (σ : Fin n → ℝ) :
    d.mixedComponentPairingValue ε β τ τ' σ d.1.externalComponentPart =
      orderedTwoPointPairingValue ε β i j τ τ' (d.externalPieceTimes σ)
        d.externalPiece.vertexLabelSequence
        (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)) := by
  classical
  have hpair : ∀ x : d.MixedComponentPair τ τ' σ d.1.externalComponentPart,
      mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
          d.externalPiece.vertexLabelSequence
          (d.externalPieceComponentPairEquiv τ τ' σ x).1.1
          (d.externalPieceComponentPairEquiv τ τ' σ x).1.2 =
        d.mixedPairContractionValue ε β τ τ' σ x.1 := by
    intro x
    have hpos := d.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x
    have hfirst : d.externalPieceMixedPosition τ τ' σ
        (d.externalPieceComponentPairEquiv τ τ' σ x).1.1 = x.1.1.1 :=
      congrArg Prod.fst hpos
    have hsecond : d.externalPieceMixedPosition τ τ' σ
        (d.externalPieceComponentPairEquiv τ τ' σ x).1.2 = x.1.1.2 :=
      congrArg Prod.snd hpos
    rw [← d.mixedTimeOrderedAtomicPairValue_externalPieceMixedPosition ε β τ τ' σ,
      FixedExternalTwoPointWickDiagram.mixedPairContractionValue, hfirst, hsecond]
  have hprod :
      (∏ pr ∈ (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).pairs,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2) =
        ∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart,
          d.mixedPairContractionValue ε β τ τ' σ pr.1 := by
    calc
      (∏ pr ∈ (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).pairs,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2) =
          ∏ pr : (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).NormalizedPair,
            mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
              d.externalPiece.vertexLabelSequence pr.1.1 pr.1.2 :=
        Finset.prod_subtype
          (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).pairs
          (fun _ => Iff.rfl)
          (fun pr => mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2)
      _ = ∏ x : d.MixedComponentPair τ τ' σ d.1.externalComponentPart,
            mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
              d.externalPiece.vertexLabelSequence
              (d.externalPieceComponentPairEquiv τ τ' σ x).1.1
              (d.externalPieceComponentPairEquiv τ τ' σ x).1.2 :=
        (Equiv.prod_comp (d.externalPieceComponentPairEquiv τ τ' σ)
          (fun pr => mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1.1 pr.1.2)).symm
      _ = ∏ pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart,
            d.mixedPairContractionValue ε β τ τ' σ pr.1 :=
        Finset.prod_congr rfl fun x _ => hpair x
  have hweight :
      d.mixedComponentWeight Common.Statistics.fermion τ τ' σ d.1.externalComponentPart =
        (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).weight
          Common.Statistics.fermion := by
    rw [FixedExternalTwoPointWickDiagram.mixedComponentWeight,
      d.mixedComponentCrossingCount_externalComponentPart]
    rfl
  rw [FixedExternalTwoPointWickDiagram.mixedComponentPairingValue, hweight, ← hprod]
  rfl

end Fermionic
end SecondQuantization
