import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiecePairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVertexProduct

set_option linter.style.header false

/-!
# External-component amplitude as the standalone external piece

The external component is already represented as the standalone `externalPiece`, with its mixed
pairing value transported exactly.  The remaining scalar transport is the quartic coupling product,
which is invariant under the same slot relabeling.  Combining those two facts identifies the
component-local fixed-time and Dyson-signed values with the ordinary fixed-time values of the
standalone piece at its inherited interaction times.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The external component's coupling product is the ordinary slot-indexed coupling weight of the
standalone external piece. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight_externalComponentPart_eq_externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) :
    d.mixedComponentVertexWeight g d.1.externalComponentPart =
      orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence := by
  classical
  rw [d.mixedComponentVertexWeight_external_eq_restricted]
  calc
    (∏ v : ↥d.1.externalInteractionPart,
        g (d.1.restrictExternalComponent.vertexLabel v)) =
        ∏ v : ↥d.1.externalInteractionPart,
          g (d.1.externalVacuumSplit.1.vertexLabel v) := by
      rw [d.1.restrictExternalComponent_eq_externalVacuumSplit_fst]
    _ = ∏ v : ↥(Finset.univ : Finset (Fin d.1.externalInteractionPart.card)),
          g (d.externalPiece.1.vertexLabel v) := by
      simpa [FixedExternalTwoPointWickDiagram.externalPiece] using
        (Common.TwoPointDiagram.prod_vertexLabel_slotCongr
          d.externalSlotEquiv d.1.externalVacuumSplit.1 g).symm
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
      d.externalPiece.fixedTimeAmplitude ε β g τ τ' (d.externalPieceTimes σ) := by
  unfold FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  rw [d.mixedComponentVertexWeight_externalComponentPart_eq_externalPiece g,
    d.mixedComponentPairingValue_externalComponentPart ε β τ τ' σ]
  change
    twoPointExternalOrderSign τ τ' *
        (orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence *
          orderedTwoPointPairingValue ε β i j τ τ' (d.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence
            (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))) =
      twoPointExternalOrderSign τ τ' *
        orderedTwoPointVertexWeight g d.externalPiece.vertexLabelSequence *
          orderedTwoPointPairingValue ε β i j τ τ' (d.externalPieceTimes σ)
            d.externalPiece.vertexLabelSequence
            (d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ))
  ring

/-- The Dyson-signed external factor is the standalone external piece's Dyson-signed fixed-time
amplitude at its inherited interaction times. -/
theorem FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue_eq_externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedExternalDysonFixedTimeValue ε β g τ τ' σ =
      d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.externalPieceTimes σ) := by
  unfold FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue
  rw [d.mixedExternalFixedTimeValue_eq_externalPiece ε β g τ τ' σ]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonSign
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  rfl

end Fermionic
end SecondQuantization
