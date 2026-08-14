import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalPiecePairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPieceField

set_option linter.style.header false

/-!
# Fermionic value of the standalone external component

Common owns the equivalence between mixed pairs of the ambient external component and normalized
pairs of the standalone external piece, including endpoint and crossing-count transport. This module
adds only the fermionic contraction value carried by that structural equivalence.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

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
    rw [← d.mixedTimeOrderedAtomicPairValue_externalPieceMixedPosition ε β τ τ' σ,
      FixedExternalTwoPointWickDiagram.mixedPairContractionValue, hfirst, hsecond]
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

end Fermionic
end SecondQuantization
