import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalPiecePairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr

set_option linter.style.header false

/-!
# External-component amplitude as the standalone external piece

The external component is represented by the standalone `externalPiece`.  This file owns the whole
fermionic value-transport chain from ambient/piece field agreement, through pair contractions and
pairing values, to the coupling-weighted fixed-time and Dyson-signed amplitudes.  The intermediate
transport lemmas are proof-local; the public endpoints identify the complete external factor with the
ordinary amplitude of the standalone piece at its inherited interaction times.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
private theorem FixedExternalTwoPointWickDiagram.orderedTwoPointLegField_orderedTwoPointLegMap
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (leg : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
    orderedTwoPointLegField i j τ τ' d.vertexLabelSequence σ
        (orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl) leg) =
      orderedTwoPointLegField i j τ τ' d.externalPiece.vertexLabelSequence
        (d.1.externalPieceTimes σ) leg := by
  cases leg with
  | inl e => rfl
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp only [orderedTwoPointLegMap_inr, orderedTwoPointLegField,
        orderedTwoPointLegTime, orderedTwoPointLegFieldLabel]
      unfold FixedExternalTwoPointWickDiagram.vertexLabelSequence
      unfold FixedExternalTwoPointWickDiagram.externalPiece
      rw [d.1.externalPiece_vertexLabel]
      rfl

omit [Fintype Mode] in
private theorem
    FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicFieldFamily_externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (ε : Mode → ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    mixedTimeOrderedAtomicFieldFamily ε i j τ τ' d.vertexLabelSequence σ
        (d.1.externalPieceMixedPosition τ τ' σ p) =
      mixedTimeOrderedAtomicFieldFamily ε i j τ τ' d.externalPiece.vertexLabelSequence
        (d.1.externalPieceTimes σ) p := by
  rw [mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField,
    mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField,
    d.1.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition,
    d.orderedTwoPointLegField_orderedTwoPointLegMap]

private theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_externalComponentPart
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
          (d.1.externalPieceComponentPairEquiv τ τ' σ x).1.1
          (d.1.externalPieceComponentPairEquiv τ τ' σ x).1.2 =
        d.mixedPairContractionValue ε β τ τ' σ x.1 := by
    intro x
    have hpos := d.1.externalPieceMixedPosition_externalPieceComponentPairEquiv τ τ' σ x
    have hfirst : d.1.externalPieceMixedPosition τ τ' σ
        (d.1.externalPieceComponentPairEquiv τ τ' σ x).1.1 = x.1.1.1 :=
      congrArg Prod.fst hpos
    have hsecond : d.1.externalPieceMixedPosition τ τ' σ
        (d.1.externalPieceComponentPairEquiv τ τ' σ x).1.2 = x.1.1.2 :=
      congrArg Prod.snd hpos
    unfold FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    simp only [mixedTimeOrderedAtomicPairValue, mixedTimeOrderedAtomicOperatorFamily]
    rw [← d.mixedTimeOrderedAtomicFieldFamily_externalPieceMixedPosition ε τ τ' σ,
      ← d.mixedTimeOrderedAtomicFieldFamily_externalPieceMixedPosition ε τ τ' σ,
      hfirst, hsecond]
  have hprod :
      (∏ pr ∈ (d.1.externalPiece.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2) =
        ∏ pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
          d.mixedPairContractionValue ε β τ τ' σ pr.1 := by
    calc
      (∏ pr ∈ (d.1.externalPiece.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2) =
          ∏ pr : (d.1.externalPiece.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).NormalizedPair,
            mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
              d.externalPiece.vertexLabelSequence pr.1.1 pr.1.2 :=
        Finset.prod_subtype
          (d.1.externalPiece.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).pairs
          (fun _ => Iff.rfl)
          (fun pr => mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1 pr.2)
      _ = ∏ x : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
            mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
              d.externalPiece.vertexLabelSequence
              (d.1.externalPieceComponentPairEquiv τ τ' σ x).1.1
              (d.1.externalPieceComponentPairEquiv τ τ' σ x).1.2 :=
        (Equiv.prod_comp (d.1.externalPieceComponentPairEquiv τ τ' σ)
          (fun pr => mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence pr.1.1 pr.1.2)).symm
      _ = ∏ pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
            d.mixedPairContractionValue ε β τ τ' σ pr.1 :=
        Finset.prod_congr rfl fun x _ => hpair x
  have hweight :
      d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ d.1.externalComponentPart =
        (d.1.externalPiece.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ)).weight
          Common.Statistics.fermion := by
    rw [Common.TwoPointDiagram.mixedComponentWeight,
      d.1.mixedComponentCrossingCount_externalComponentPart]
    rfl
  rw [FixedExternalTwoPointWickDiagram.mixedComponentPairingValue, hweight, ← hprod]
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
private theorem
    FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight_externalComponentPart_eq_externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) :
    d.mixedComponentVertexWeight g d.1.externalComponentPart =
      orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence := by
  classical
  calc
    d.mixedComponentVertexWeight g d.1.externalComponentPart =
        ∏ v : ↥d.1.externalInteractionPart,
          g (d.1.externalVacuumSplit.1.vertexLabel v) := by
      unfold FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight
      apply Finset.prod_congr rfl
      intro v _
      rw [Common.TwoPointDiagram.externalVacuumSplit_fst_vertexLabel]
    _ = ∏ v : ↥(Finset.univ : Finset (Fin d.1.externalInteractionPart.card)),
          g (d.externalPiece.1.vertexLabel v) := by
      let e := Common.standardSlotEquiv d.1.externalInteractionPart
      rw [← Equiv.prod_comp e
        (fun v => g (d.externalPiece.1.vertexLabel v))]
      apply Finset.prod_congr rfl
      intro v _
      simp [FixedExternalTwoPointWickDiagram.externalPiece,
        Common.TwoPointDiagram.externalPiece, e]
    _ = orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence := by
      unfold orderedTwoPointVertexWeight FixedExternalTwoPointWickDiagram.vertexLabelSequence
      let e : Fin d.1.externalInteractionPart.card ≃
          ↥(Finset.univ : Finset (Fin d.1.externalInteractionPart.card)) :=
        (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)).symm
      simpa [e] using
        (Equiv.prod_comp e
          (fun v : ↥(Finset.univ : Finset (Fin d.1.externalInteractionPart.card)) =>
            g (d.externalPiece.1.vertexLabel v))).symm

/-- The complete external fixed-time factor is the fixed-time amplitude of the standalone external
piece at the interaction times inherited from the ambient diagram. -/
theorem FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue_eq_externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedExternalFixedTimeValue ε β g τ τ' σ =
      d.externalPiece.fixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) := by
  unfold FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  rw [d.mixedComponentVertexWeight_externalComponentPart_eq_externalPiece g,
    d.mixedComponentPairingValue_externalComponentPart ε β τ τ' σ]
  change
    twoPointExternalOrderSign τ τ' *
        (orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence *
          orderedTwoPointPairingValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence
            (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ))) =
      twoPointExternalOrderSign τ τ' *
        orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence *
          orderedTwoPointPairingValue ε β i j τ τ' (d.1.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence
            (d.externalPiece.1.pairingInMixedOrder τ τ' (d.1.externalPieceTimes σ))
  ring

/-- The Dyson-signed external factor is the standalone external piece's Dyson-signed fixed-time
amplitude at its inherited interaction times. -/
theorem FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue_eq_externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedExternalDysonFixedTimeValue ε β g τ τ' σ =
      d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) := by
  unfold FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue
  rw [d.mixedExternalFixedTimeValue_eq_externalPiece ε β g τ τ' σ]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonSign
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  rfl

end Fermionic
end SecondQuantization
