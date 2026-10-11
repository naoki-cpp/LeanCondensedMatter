import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.NormalizedPairRestriction

set_option linter.style.header false

/-!
# Mixed-time pairing restrictions, component pairs, and transports

The pairing partner preserves every full graph component of a two-point diagram. This module
restricts that partner to mixed-time component positions, identifies normalized pairs within each
component, and transports pairs through vacuum coordinates and between time assignments.
Normalization may swap endpoint order. All constructions are statistics-independent.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The mixed-order pairing partner remains in the same full component. -/
@[simp]
theorem TwoPointDiagram.mixedPositionComponent_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    d.mixedPositionComponent τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) =
      d.mixedPositionComponent τ τ' σ p := by
  apply Subtype.ext
  change d.vertexGraph.componentBlock
      (twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          ((d.pairingInMixedOrder τ τ' σ).partner p))) =
    d.vertexGraph.componentBlock
      (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p))
  rw [TwoPointDiagram.pairingInMixedOrder, PairingOn.transport_partner,
    Equiv.apply_symm_apply]
  exact (d.pairing.vertexGraph_componentBlock_partner twoPointVertexOfLeg _).symm

/-- The full diagram component containing a normalized pair of the mixed-time pairing. -/
noncomputable def TwoPointDiagram.mixedPairComponent
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) :
    d.vertexGraph.componentPartition.parts :=
  d.mixedPositionComponent τ τ' σ pr.1.1

/-- Normalized mixed-time pairs assigned to one full diagram component. -/
abbrev TwoPointDiagram.MixedComponentPair
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :=
  {pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair //
    d.mixedPairComponent τ τ' σ pr = B}

/-- The two selected endpoints of mixed component pairs are equivalent to all mixed positions of the
component. -/
noncomputable def TwoPointDiagram.mixedComponentPairEndpointEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B × Fin 2 ≃ d.MixedComponentPosition τ τ' σ B :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEndpointEquiv
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])

/-- The ambient position of a mixed component pair endpoint is its normalized-pair endpoint. -/
@[simp]
theorem TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_val
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) (k : Fin 2) :
    (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)).1 =
      (d.pairingInMixedOrder τ τ' σ).pairEndpoint (pr.1, k) := by
  unfold TwoPointDiagram.mixedComponentPairEndpointEquiv
  exact Pairing.normalizedPairSubtypeEndpointEquiv_apply_val
    (d.pairingInMixedOrder τ τ' σ)
    (fun p => d.mixedPositionComponent τ τ' σ p = B) _ pr k

/-- Mixed pairs in a vacuum component are equivalent to normalized pairs of the corresponding
restricted vacuum pairing. -/
noncomputable def TwoPointDiagram.mixedVacuumComponentPairEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hVac : ComponentIsVacuum (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))) :
    d.MixedComponentPair τ τ' σ B ≃ (d.restrictedVacuumPairing B hVac).NormalizedPair :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEquivOfEndpointEquiv
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])
    ((d.mixedComponentPositionEquiv τ τ' σ B).trans
      (d.vacuumBlockLegEquiv B hVac))
    (d.restrictedVacuumPairing B hVac)
    (fun pos => by
      change (d.pairing.restrictAlongEquiv (d.legInComponent B)
          (fun i => d.legInComponent_partner_iff B i)
          (d.vacuumBlockLegEquiv B hVac)).partner
            (d.vacuumBlockLegEquiv B hVac
              (d.mixedComponentPositionEquiv τ τ' σ B pos)) =
        d.vacuumBlockLegEquiv B hVac
          (d.mixedComponentPositionEquiv τ τ' σ B
            (((d.pairingInMixedOrder τ τ' σ).restrict
              (fun q => d.mixedPositionComponent τ τ' σ q = B)
              (fun q => by rw [d.mixedPositionComponent_partner])).partner pos))
      rw [d.pairing.restrictAlongEquiv_partner]
      apply congrArg (d.vacuumBlockLegEquiv B hVac)
      apply Subtype.ext
      change d.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' σ pos) =
        mixedTimeAmbientPositionEquiv τ τ' σ
          (((d.pairingInMixedOrder τ τ' σ).restrict
            (fun q => d.mixedPositionComponent τ τ' σ q = B)
            (fun q => by rw [d.mixedPositionComponent_partner])).partner pos)
      rw [PairingOn.restrict_partner_val, TwoPointDiagram.pairingInMixedOrder,
        PairingOn.transport_partner, Equiv.apply_symm_apply])

/-- Canonical comparison of mixed normalized pairs in one component, obtained by restricting the
global partner-preserving pair transport rather than splitting external and vacuum components. -/
noncomputable def TwoPointDiagram.mixedComponentPairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B ≃ d.MixedComponentPair τ τ' υ B := by
  let f := (mixedTimeAmbientPositionEquiv τ τ' σ).trans
    (mixedTimeAmbientPositionEquiv τ τ' υ).symm
  have hpos (p : Fin (2 * (2 * n + 1))) :
      d.mixedPositionComponent τ τ' υ (f p) =
        d.mixedPositionComponent τ τ' σ p := by
    apply Subtype.ext
    change d.vertexGraph.componentBlock
        (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' υ (f p))) =
      d.vertexGraph.componentBlock
        (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p))
    simp only [f, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEquivOfPartnerEquiv
    (d.pairingInMixedOrder τ τ' υ) f
    (fun p => by
      simp only [f, TwoPointDiagram.pairingInMixedOrder,
        PairingOn.transport_partner, Equiv.trans_apply,
        Equiv.apply_symm_apply])
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => d.mixedPositionComponent τ τ' υ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])
    (fun p => by rw [hpos])

end Common
end SecondQuantization
