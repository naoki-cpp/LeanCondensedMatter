import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairProduct

set_option linter.style.header false

/-!
# Fermionic contraction products over mixed two-point components

Common owns the mixed-pair component fibers and their generic commutative-product factorization.
This module adds only the canonical free Gibbs contraction values and their fermionic pairing-value
specializations.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction attached to one normalized pair in the actual
mixed-time pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.1.pairingInMixedOrder τ τ' σ).NormalizedPair) : ℂ :=
  mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ d.vertexLabelSequence
    pr.1.1 pr.1.2

/-- The canonical pairing value exposes the component-factorized contraction product while retaining
the global mixed-order fermionic pairing weight. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointPairingValue_eq_weight_mul_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
        (d.1.pairingInMixedOrder τ τ' σ) =
      (d.1.pairingInMixedOrder τ τ' σ).weight Common.Statistics.fermion *
        ((∏ pr : d.1.MixedComponentPair τ τ' σ d.1.externalComponentPart,
          d.mixedPairContractionValue ε β τ τ' σ pr.1) *
          d.1.vacuumComponentParts.prod (fun B =>
            ∏ pr : d.1.MixedComponentPair τ τ' σ B,
              d.mixedPairContractionValue ε β τ τ' σ pr.1)) := by
  unfold orderedTwoPointPairingValue Combinatorics.Pairing.evaluation
  rw [d.1.prod_mixedPairValues_eq_external_mul_prod_vacuum τ τ' σ]
  rfl

/-- A restricted vacuum-pair value is defined by pulling back to its unique original mixed-time
pair. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedVacuumRestrictedPairContractionValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B)
    (pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair) : ℂ :=
  d.mixedPairContractionValue ε β τ τ' σ
    ((d.1.mixedVacuumComponentPairEquiv τ τ' σ B hVac).symm pr).1

/-- One vacuum-component contraction product reindexes to its restricted vacuum pairing without an
endpoint-orientation assumption. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedVacuumPairContractionValue_eq_restricted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B) :
    (∏ pr : d.1.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1) =
      ∏ pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair,
        d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac pr := by
  calc
    (∏ pr : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ pr.1) =
      ∏ pr : d.1.MixedComponentPair τ τ' σ B,
        d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac
          (d.1.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr) := by
        apply Fintype.prod_congr
        intro pr
        simp [FixedExternalTwoPointWickDiagram.mixedVacuumRestrictedPairContractionValue]
    _ = ∏ pr : (d.1.restrictedVacuumPairing B hVac).NormalizedPair,
        d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac pr :=
      Equiv.prod_comp (d.1.mixedVacuumComponentPairEquiv τ τ' σ B hVac)
        (d.mixedVacuumRestrictedPairContractionValue ε β τ τ' σ B hVac)

end Fermionic
end SecondQuantization
