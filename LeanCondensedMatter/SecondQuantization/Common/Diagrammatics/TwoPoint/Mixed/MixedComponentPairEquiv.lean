import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.NormalizedPairRestriction

set_option linter.style.header false

/-!
# Mixed-time component pairs and local pairings

This module lifts generic mixed component-position transport to normalized pairs. Each full component
is identified with the corresponding time-independent restricted pairing; normalized endpoint order
may be preserved or swapped. Canonical comparisons across time assignments factor through these
restricted pairings. No particle-statistics or operator data enter these constructions.
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

/-- Mixed pairs in the external component are equivalent to normalized pairs of the canonical
external split pairing. -/
noncomputable def TwoPointDiagram.mixedExternalComponentPairEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.MixedComponentPair τ τ' σ d.externalComponentPart ≃
      d.externalVacuumSplit.1.pairing.NormalizedPair :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairSubtypeEquivOfEndpointEquiv
    (fun p => d.mixedPositionComponent τ τ' σ p = d.externalComponentPart)
    (fun p => by rw [d.mixedPositionComponent_partner])
    (d.mixedExternalPositionEquiv τ τ' σ) d.externalVacuumSplit.1.pairing
    (fun pos => by
      simpa only [TwoPointDiagram.mixedRestrictedPartner] using
        d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' σ pos)

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
  apply (mixedTimeAmbientPositionEquiv τ τ' υ).injective
  calc
    mixedTimeAmbientPositionEquiv τ τ' υ
        ((d.pairingInMixedOrder τ τ' υ).partner
          (((mixedTimeAmbientPositionEquiv τ τ' σ).trans
            (mixedTimeAmbientPositionEquiv τ τ' υ).symm) p)) =
      d.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' υ
        (((mixedTimeAmbientPositionEquiv τ τ' σ).trans
          (mixedTimeAmbientPositionEquiv τ τ' υ).symm) p)) :=
        d.mixedTimeAmbientPositionEquiv_partner τ τ' υ _
    _ = d.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' σ p) := by simp
    _ = mixedTimeAmbientPositionEquiv τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) :=
      (d.mixedTimeAmbientPositionEquiv_partner τ τ' σ p).symm
    _ = mixedTimeAmbientPositionEquiv τ τ' υ
        (((mixedTimeAmbientPositionEquiv τ τ' σ).trans
          (mixedTimeAmbientPositionEquiv τ τ' υ).symm)
          ((d.pairingInMixedOrder τ τ' σ).partner p)) := by simp

/-- Transport ambient normalized pairs between time assignments through their common diagram legs. -/
noncomputable def TwoPointDiagram.mixedPairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).NormalizedPair ≃
      (d.pairingInMixedOrder τ τ' υ).NormalizedPair :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPairEquivOfPartnerEquiv
    (d.pairingInMixedOrder τ τ' υ)
    ((mixedTimeAmbientPositionEquiv τ τ' σ).trans
      (mixedTimeAmbientPositionEquiv τ τ' υ).symm)
    (d.mixedTimePositionEquiv_partner τ τ' σ υ)

/-- Ambient pair transport preserves the pair endpoints up to normalized orientation. -/
theorem TwoPointDiagram.mixedPairTimeEquiv_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) :
    let f := (mixedTimeAmbientPositionEquiv τ τ' σ).trans
      (mixedTimeAmbientPositionEquiv τ τ' υ).symm
    (d.mixedPairTimeEquiv τ τ' σ υ pr).1 =
      (f pr.1.1, f pr.1.2) ∨
    (d.mixedPairTimeEquiv τ τ' σ υ pr).1 =
      (f pr.1.2, f pr.1.1) := by
  dsimp only
  exact (d.pairingInMixedOrder τ τ' σ).normalizedPairEquivOfPartnerEquiv_pair_eq_or_swap
    (d.pairingInMixedOrder τ τ' υ)
    ((mixedTimeAmbientPositionEquiv τ τ' σ).trans
      (mixedTimeAmbientPositionEquiv τ τ' υ).symm)
    (d.mixedTimePositionEquiv_partner τ τ' σ υ) pr

/-- Canonical comparison of mixed normalized pairs in one component, obtained by restricting the
global partner-preserving pair transport rather than splitting external and vacuum components. -/
noncomputable def TwoPointDiagram.mixedComponentPairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B ≃ d.MixedComponentPair τ τ' υ B := by
  classical
  let f := (mixedTimeAmbientPositionEquiv τ τ' σ).trans
    (mixedTimeAmbientPositionEquiv τ τ' υ).symm
  let e := d.mixedPairTimeEquiv τ τ' σ υ
  have hpos (p : Fin (2 * (2 * n + 1))) :
      d.mixedPositionComponent τ τ' υ (f p) =
        d.mixedPositionComponent τ τ' σ p := by
    apply Subtype.ext
    change d.vertexGraph.componentBlock
        (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' υ (f p))) =
      d.vertexGraph.componentBlock
        (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p))
    simp [f]
  have hcomp (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) :
      d.mixedPairComponent τ τ' υ (e pr) =
        d.mixedPairComponent τ τ' σ pr := by
    have hends := d.mixedPairTimeEquiv_pair_eq_or_swap τ τ' σ υ pr
    change (e pr).1 = (f pr.1.1, f pr.1.2) ∨
        (e pr).1 = (f pr.1.2, f pr.1.1) at hends
    change d.mixedPositionComponent τ τ' υ (e pr).1.1 =
      d.mixedPositionComponent τ τ' σ pr.1.1
    rcases hends with hends | hends
    · rw [congrArg Prod.fst hends, hpos]
    · rw [congrArg Prod.fst hends, hpos]
      have hpair := ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff
        pr.1.1 pr.1.2).1 pr.2
      rw [← hpair.2, d.mixedPositionComponent_partner]
  exact e.subtypeEquiv (fun pr => by
    change d.mixedPairComponent τ τ' σ pr = B ↔
      d.mixedPairComponent τ τ' υ (e pr) = B
    rw [hcomp])

end Common
end SecondQuantization
