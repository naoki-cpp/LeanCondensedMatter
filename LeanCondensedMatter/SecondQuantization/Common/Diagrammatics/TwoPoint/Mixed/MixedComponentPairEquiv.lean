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
  rw [d.mixedTimeAmbientPositionEquiv_partner]
  exact (d.pairing.vertexGraph_componentBlock_partner twoPointVertexOfLeg _).symm

/-- The mixed-order partner restricted to one full component-position fiber. -/
noncomputable def TwoPointDiagram.mixedRestrictedPartner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    Equiv.Perm (d.MixedComponentPosition τ τ' σ B) :=
  ((d.pairingInMixedOrder τ τ' σ).restrict
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])).partner

/-- The restricted mixed partner has the ambient mixed position as its underlying value. -/
theorem TwoPointDiagram.mixedRestrictedPartner_val
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    (d.mixedRestrictedPartner τ τ' σ B p : Fin (2 * (2 * n + 1))) =
      (d.pairingInMixedOrder τ τ' σ).partner p := by
  simpa only [TwoPointDiagram.mixedRestrictedPartner] using
    (d.pairingInMixedOrder τ τ' σ).restrict_partner_val
      (fun q => d.mixedPositionComponent τ τ' σ q = B)
      (fun q => by rw [d.mixedPositionComponent_partner]) p

/-- The mixed component-position equivalence intertwines the mixed restricted partner with the
standard component restricted partner. -/
private theorem TwoPointDiagram.mixedComponentPositionEquiv_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionEquiv τ τ' σ B
        (d.mixedRestrictedPartner τ τ' σ B p) =
      d.restrictedPartner (B : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n))))
        (d.mixedComponentPositionEquiv τ τ' σ B p) := by
  apply Subtype.ext
  change mixedTimeAmbientPositionEquiv τ τ' σ
      (d.mixedRestrictedPartner τ τ' σ B p) =
    (d.restrictedPartner (B : Finset (TwoPointVertex
      (Finset.univ : Finset (Fin n))))
      (d.mixedComponentPositionEquiv τ τ' σ B p) :
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)))
  rw [d.mixedRestrictedPartner_val, d.mixedTimeAmbientPositionEquiv_partner,
    d.restrictedPartner_val]
  apply congrArg d.pairing.partner
  rfl

/-- A vacuum restricted pairing partner is the transport of the corresponding mixed restricted
partner. -/
private theorem TwoPointDiagram.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hVac : ComponentIsVacuum (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (p : d.MixedComponentPosition τ τ' σ B) :
    (d.restrictedVacuumPairing B hVac).partner
        (d.mixedVacuumPositionEquiv τ τ' σ B hVac p) =
      d.mixedVacuumPositionEquiv τ τ' σ B hVac
        (d.mixedRestrictedPartner τ τ' σ B p) := by
  change (d.restrictedVacuumPairing B hVac).partner
      (d.vacuumBlockLegEquiv B hVac
        (d.mixedComponentPositionEquiv τ τ' σ B p)) =
    d.vacuumBlockLegEquiv B hVac
      (d.mixedComponentPositionEquiv τ τ' σ B
        (d.mixedRestrictedPartner τ τ' σ B p))
  rw [d.mixedComponentPositionEquiv_partner]
  simpa only [TwoPointDiagram.restrictedVacuumPairing, TwoPointDiagram.restrictedPartner] using
    d.pairing.restrictAlongEquiv_partner (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff B i) (d.vacuumBlockLegEquiv B hVac)
      (d.mixedComponentPositionEquiv τ τ' σ B p)

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

/-- On mixed component endpoints, the restricted mixed partner exchanges endpoint zero and endpoint
one of the same normalized mixed pair. -/
theorem TwoPointDiagram.mixedRestrictedPartner_componentPairEndpoint_zero
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedRestrictedPartner τ τ' σ B
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) =
      d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1) := by
  apply Subtype.ext
  rw [d.mixedRestrictedPartner_val]
  exact (((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1.1 pr.1.1.2).1 pr.1.2).2

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
    (d.mixedVacuumPositionEquiv τ τ' σ B hVac)
    (d.restrictedVacuumPairing B hVac)
    (fun pos => by
      simpa only [TwoPointDiagram.mixedRestrictedPartner] using
        d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' σ B hVac pos)

/-- Mixed-time coordinate transport intertwines the partners of the two ambient pairings. -/
private theorem TwoPointDiagram.mixedTimePositionEquiv_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    (d.pairingInMixedOrder τ τ' υ).partner
        (((mixedTimeAmbientPositionEquiv τ τ' σ).trans
          (mixedTimeAmbientPositionEquiv τ τ' υ).symm) p) =
      ((mixedTimeAmbientPositionEquiv τ τ' σ).trans
        (mixedTimeAmbientPositionEquiv τ τ' υ).symm)
          ((d.pairingInMixedOrder τ τ' σ).partner p) := by
  simp only [TwoPointDiagram.pairingInMixedOrder, PairingOn.transport_partner,
    Equiv.trans_apply, Equiv.apply_symm_apply]

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
    (d.mixedTimePositionEquiv_partner τ τ' σ υ)
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => d.mixedPositionComponent τ τ' υ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])
    (fun p => by rw [hpos])

end Common
end SecondQuantization
