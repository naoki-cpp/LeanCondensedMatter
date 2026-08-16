import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingEven
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude

set_option linter.style.header false

/-!
# Component-local mixed-time pairing values

Common owns mixed component pair fibers, crossing counts, and statistics weights. This module combines
the fermionic component weight with canonical free Gibbs contraction products and feeds that physical
component value into the fixed-time amplitude.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fermionic crossing weight times the contraction product internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
    ∏ pr : d.1.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1

/-- The full mixed-order pairing value is the product of the pairing values of all full
components. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointPairingValue_eq_prod_components_unconditional
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
        (d.1.pairingInMixedOrder τ τ' σ) =
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentPairingValue ε β τ τ' σ B := by
  rw [d.orderedTwoPointPairingValue_eq_weight_mul_components,
    d.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum_unconditional]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
  rw [← d.1.prod_componentParts_eq_external_mul_prod_vacuum
    (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ)]
  rw [← d.1.prod_componentParts_eq_external_mul_prod_vacuum
    (fun B =>
      ∏ pr : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ pr.1)]
  rw [Finset.prod_mul_distrib]

end Fermionic
end SecondQuantization
