import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue

set_option linter.style.header false

/-!
# Component-local fixed-time values for two-point diagrams

A fixed-time two-point Wick-diagram amplitude contains three scalar layers: the external-field time-
ordering sign, the product of quartic couplings, and the mixed-order pairing value. The preceding
modules factor the pairing value over full external-plus-interaction components, while the common
two-point component API factors arbitrary interaction-vertex products.

This module combines those results into component-local fixed-time values and the all-component
factorization. The external value is related to the standalone external piece downstream in
`ExternalPieceAmplitude`.

The Dyson sign and ordered-simplex integration are intentionally left to the next layer.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Product of quartic couplings on the interaction vertices belonging to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ)
    (B : d.1.componentPartition.parts) : ℂ :=
  ∏ v : ↥(Common.TwoPointDiagram.interactionPart
      (B : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))),
    g (d.1.vertexLabel
      ⟨v.1, Common.TwoPointDiagram.interactionPart_subset
        (B : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n)))) v.2⟩)

section Fermionic

variable [LinearOrder Mode] [Fintype Mode]

/-- Coupling weight times mixed pairing value internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.mixedComponentVertexWeight g B *
    d.mixedComponentPairingValue ε β τ τ' σ B

/-- The canonical external fixed-time value also carries the external-field ordering sign. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  twoPointExternalOrderSign τ τ' *
    d.mixedComponentFixedTimeValue ε β g τ τ' σ d.1.externalComponentPart

/-- The global fixed-time amplitude is the external ordering sign times the product of all
component-local fixed-time values. -/
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_eq_externalSign_mul_prod_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.fixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          d.mixedComponentFixedTimeValue ε β g τ τ' σ B := by
  change twoPointExternalOrderSign τ τ' *
      orderedTwoPointVertexWeight g d.vertexLabelSequence *
        orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
          (d.1.pairingInMixedOrder τ τ' σ) = _
  have hvertex :
      orderedTwoPointVertexWeight g d.vertexLabelSequence =
        ∏ B : d.1.componentPartition.parts,
          d.mixedComponentVertexWeight g B := by
    classical
    calc
      orderedTwoPointVertexWeight g d.vertexLabelSequence =
          ∏ v : ↥(Finset.univ : Finset (Fin n)), g (d.1.vertexLabel v) := by
        let e : Fin n ≃ ↥(Finset.univ : Finset (Fin n)) :=
          (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)).symm
        simpa [orderedTwoPointVertexWeight,
          FixedExternalTwoPointWickDiagram.vertexLabelSequence, e] using
          (Equiv.prod_comp e
            (fun v : ↥(Finset.univ : Finset (Fin n)) => g (d.1.vertexLabel v)))
      _ = ∏ B : d.1.componentPartition.parts,
          ∏ v : ↥(Common.TwoPointDiagram.interactionPart
            (B : Finset (Common.TwoPointVertex
              (Finset.univ : Finset (Fin n))))),
            g (d.1.vertexLabel
              ⟨v.1, Common.TwoPointDiagram.interactionPart_subset
                (B : Finset (Common.TwoPointVertex
                  (Finset.univ : Finset (Fin n)))) v.2⟩) :=
        d.1.prod_vertexLabel_eq_prod_componentInteractionParts g
      _ = ∏ B : d.1.componentPartition.parts,
          d.mixedComponentVertexWeight g B := rfl
  have hpairing :
      orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
          (d.1.pairingInMixedOrder τ τ' σ) =
        ∏ B : d.1.componentPartition.parts,
          d.mixedComponentPairingValue ε β τ τ' σ B := by
    unfold orderedTwoPointPairingValue Combinatorics.Pairing.evaluation
    rw [d.1.prod_mixedPairValues_eq_external_mul_prod_vacuum τ τ' σ,
      d.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum_unconditional]
    unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
      FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    rw [← d.1.prod_componentParts_eq_external_mul_prod_vacuum
      (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ)]
    rw [← d.1.prod_componentParts_eq_external_mul_prod_vacuum
      (fun B =>
        ∏ pr : d.1.MixedComponentPair τ τ' σ B,
          mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ d.vertexLabelSequence
            pr.1.1.1 pr.1.1.2)]
    rw [Finset.prod_mul_distrib]
  rw [hvertex, hpairing]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  rw [Finset.prod_mul_distrib]
  ring

end Fermionic

end Fermionic
end SecondQuantization
