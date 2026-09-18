import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.NormalizedPairRestriction

set_option linter.style.header false

/-!
# Mixed-time component pairs and local pairings

This module lifts generic mixed component-position transport to normalized pairs. Each full component
is identified with the corresponding time-independent restricted pairing; normalized endpoint order
may be preserved or swapped. No particle-statistics or operator data enter these constructions.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The full diagram component containing a normalized pair of the mixed-time pairing. -/
noncomputable def TwoPointDiagram.mixedPairComponent
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) :
    d.componentPartition.parts :=
  d.mixedPositionComponent τ τ' σ pr.1.1

/-- Normalized mixed-time pairs assigned to one full diagram component. -/
abbrev TwoPointDiagram.MixedComponentPair
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :=
  {pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair //
    d.mixedPairComponent τ τ' σ pr = B}

/-- The two selected endpoints of mixed component pairs are equivalent to all mixed positions of the
component. -/
noncomputable def TwoPointDiagram.mixedComponentPairEndpointEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B × Fin 2 ≃ d.MixedComponentPosition τ τ' σ B :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEndpointEquiv
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])

@[simp]
theorem TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_zero
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)).1 = pr.1.1.1 := by
  rfl

@[simp]
theorem TwoPointDiagram.mixedComponentPairEndpointEquiv_apply_one
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)).1 = pr.1.1.2 := by
  rfl

/-- On mixed component endpoints, the restricted mixed partner exchanges endpoint zero and endpoint
one of the same normalized mixed pair. -/
theorem TwoPointDiagram.mixedRestrictedPartner_componentPairEndpoint_zero
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedRestrictedPartner τ τ' σ B
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) =
      d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1) := by
  apply Subtype.ext
  rw [d.mixedRestrictedPartner_val]
  exact (((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1.1 pr.1.1.2).1 pr.1.2).2

/-- Mixed component pairs are equivalent to normalized pairs of a local pairing obtained by
transporting the mixed restricted partner through the supplied position equivalence. -/
noncomputable def TwoPointDiagram.mixedComponentPairRestrictedEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) {m : ℕ}
    (e : d.MixedComponentPosition τ τ' σ B ≃ Fin (2 * m))
    (localPairing : Pairing m)
    (hpartner : ∀ pos,
      localPairing.partner (e pos) = e (d.mixedRestrictedPartner τ τ' σ B pos)) :
    d.MixedComponentPair τ τ' σ B ≃ localPairing.NormalizedPair :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEquivOfEndpointEquiv
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner]) e localPairing
    (fun pos => by
      simpa only [TwoPointDiagram.mixedRestrictedPartner] using hpartner pos)

/-- Mixed pairs in the external component are equivalent to normalized pairs of the canonical
external split pairing. -/
noncomputable def TwoPointDiagram.mixedExternalComponentPairEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.MixedComponentPair τ τ' σ d.externalComponentPart ≃
      d.externalVacuumSplit.1.pairing.NormalizedPair :=
  d.mixedComponentPairRestrictedEquiv τ τ' σ d.externalComponentPart
    (d.mixedExternalPositionEquiv τ τ' σ) d.externalVacuumSplit.1.pairing
    (d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' σ)

/-- Mixed pairs in a vacuum component are equivalent to normalized pairs of the corresponding
restricted vacuum pairing. -/
noncomputable def TwoPointDiagram.mixedVacuumComponentPairEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B) :
    d.MixedComponentPair τ τ' σ B ≃ (d.restrictedVacuumPairing B hVac).NormalizedPair :=
  d.mixedComponentPairRestrictedEquiv τ τ' σ B
    (d.mixedVacuumPositionEquiv τ τ' σ B hVac)
    (d.restrictedVacuumPairing B hVac)
    (d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' σ B hVac)

end Common
end SecondQuantization
