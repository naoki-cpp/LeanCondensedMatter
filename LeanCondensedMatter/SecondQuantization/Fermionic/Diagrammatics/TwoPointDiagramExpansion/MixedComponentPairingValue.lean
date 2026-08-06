import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingEven

set_option linter.style.header false

/-!
# Component-local mixed-time pairing values

The mixed two-point pairing value consists of a fermionic crossing weight and a product of finite
Gibbs contractions.  The preceding layers factor those two pieces over the full external-plus-
interaction components.  This module assembles them into one component-local pairing value and
identifies the external and vacuum factors with products over the corresponding restricted
pairings.

The contraction values on restricted pairings remain defined by pullback from the actual mixed-time
pairing.  Thus no endpoint-orientation invariance is assumed at this assembly boundary.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fermionic crossing weight times the contraction product internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
    ∏ pr : d.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1

/-- The full mixed-order pairing value is the product of the pairing values of all full
components. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointPairingValue_eq_prod_components_unconditional
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
        (d.pairingInMixedOrder τ τ' σ) =
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentPairingValue ε β τ τ' σ B := by
  rw [d.orderedTwoPointPairingValue_eq_weight_mul_components,
    d.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum_unconditional]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
  rw [← d.1.prod_componentParts_eq_external_mul_prod_vacuum
    (d.mixedComponentWeight Common.Statistics.fermion τ τ' σ)]
  rw [← d.1.prod_componentParts_eq_external_mul_prod_vacuum
    (fun B =>
      ∏ pr : d.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ pr.1)]
  rw [Finset.prod_mul_distrib]

/-- External/vacuum form of the unconditional mixed pairing-value factorization. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointPairingValue_eq_external_mul_prod_vacuum_unconditional
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
        (d.pairingInMixedOrder τ τ' σ) =
      d.mixedComponentPairingValue ε β τ τ' σ d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod
          (d.mixedComponentPairingValue ε β τ τ' σ) := by
  rw [d.orderedTwoPointPairingValue_eq_prod_components_unconditional ε β τ τ' σ,
    d.1.prod_componentParts_eq_external_mul_prod_vacuum]

/-- The external component pairing value written on the restricted external pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedExternalRestrictedPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  d.mixedComponentWeight Common.Statistics.fermion τ τ' σ d.1.externalComponentPart *
    ∏ pr : d.1.restrictedExternalPairing.NormalizedPair,
      d.mixedExternalRestrictedPairContractionValue ε β τ τ' σ pr

/-- The mixed external-component value is exactly its restricted-pairing value. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_external_eq_restricted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.mixedComponentPairingValue ε β τ τ' σ d.1.externalComponentPart =
      d.mixedExternalRestrictedPairingValue ε β τ τ' σ := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
  unfold FixedExternalTwoPointWickDiagram.mixedExternalRestrictedPairingValue
  rw [d.prod_mixedExternalPairContractionValue_eq_restricted]

/-- One vacuum-component pairing value written on its restricted vacuum pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumRestrictedPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B) : ℂ :=
  d.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
    ∏ pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair,
      d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac pr

/-- A mixed vacuum-component value is exactly its restricted-pairing value. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_vacuum_eq_restricted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B) :
    d.mixedComponentPairingValue ε β τ τ' σ B =
      d.mixedVacuumRestrictedPairingValue ε β τ τ' σ B hVac := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
  unfold FixedExternalTwoPointWickDiagram.mixedVacuumRestrictedPairingValue
  rw [d.prod_mixedVacuumPairContractionValue_eq_restricted]

/-- The fixed-time two-point amplitude exposes its global external/coupling prefactor and the
component-factorized mixed pairing value. -/
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_eq_prefactor_mul_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.fixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        orderedTwoPointVertexWeight g d.vertexLabelSequence *
          (d.mixedComponentPairingValue ε β τ τ' σ d.1.externalComponentPart *
            d.1.vacuumComponentParts.prod
              (d.mixedComponentPairingValue ε β τ τ' σ)) := by
  change twoPointExternalOrderSign τ τ' *
      orderedTwoPointVertexWeight g d.vertexLabelSequence *
        orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
          (d.pairingInMixedOrder τ τ' σ) = _
  rw [d.orderedTwoPointPairingValue_eq_external_mul_prod_vacuum_unconditional]

end Fermionic
end SecondQuantization
