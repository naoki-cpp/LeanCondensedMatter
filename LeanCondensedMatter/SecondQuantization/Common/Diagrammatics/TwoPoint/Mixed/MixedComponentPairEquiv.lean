import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

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

/-- The two endpoints of a normalized mixed-time pair determine the same full component. -/
theorem TwoPointDiagram.mixedPairComponent_second_eq_first
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) :
    d.mixedPositionComponent τ τ' σ pr.1.2 =
      d.mixedPositionComponent τ τ' σ pr.1.1 := by
  have hpr := ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
  rw [← hpr.2, d.mixedPositionComponent_partner]

/-- The first endpoint of a mixed component pair belongs to that component. -/
theorem TwoPointDiagram.mixedComponentPair_first_mem
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedPositionComponent τ τ' σ pr.1.1.1 = B := by
  simpa [TwoPointDiagram.mixedPairComponent] using pr.2

/-- The second endpoint of a mixed component pair belongs to that component. -/
theorem TwoPointDiagram.mixedComponentPair_second_mem
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedPositionComponent τ τ' σ pr.1.1.2 = B :=
  (d.mixedPairComponent_second_eq_first τ τ' σ pr.1).trans
    (d.mixedComponentPair_first_mem τ τ' σ B pr)

private theorem TwoPointDiagram.mixedPairComponent_positionToPairEndpoint_eq
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pos : d.MixedComponentPosition τ τ' σ B) :
    d.mixedPairComponent τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).positionToPairEndpoint pos.1).1 = B := by
  generalize hxdef :
    (d.pairingInMixedOrder τ τ' σ).positionToPairEndpoint pos.1 = x
  rcases x with ⟨pr, k⟩
  have hx : (d.pairingInMixedOrder τ τ' σ).pairEndpoint (pr, k) = pos.1 := by
    have h := (d.pairingInMixedOrder τ τ' σ).pairEndpointEquiv.right_inv pos.1
    change (d.pairingInMixedOrder τ τ' σ).pairEndpoint
      ((d.pairingInMixedOrder τ τ' σ).positionToPairEndpoint pos.1) = pos.1 at h
    rw [hxdef] at h
    exact h
  change d.mixedPositionComponent τ τ' σ pr.1.1 = B
  fin_cases k
  · have hfirst : pr.1.1 = pos.1 := by simpa using hx
    simpa [hfirst] using pos.2
  · have hsecond : pr.1.2 = pos.1 := by simpa using hx
    have hsecondComponent : d.mixedPositionComponent τ τ' σ pr.1.2 = B := by
      simpa [hsecond] using pos.2
    exact (d.mixedPairComponent_second_eq_first τ τ' σ pr).symm.trans hsecondComponent

/-- The two selected endpoints of mixed component pairs are equivalent to all mixed positions of the
component. -/
noncomputable def TwoPointDiagram.mixedComponentPairEndpointEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B × Fin 2 ≃ d.MixedComponentPosition τ τ' σ B where
  toFun x := by
    rcases x with ⟨pr, k⟩
    refine ⟨(d.pairingInMixedOrder τ τ' σ).pairEndpoint (pr.1, k), ?_⟩
    fin_cases k
    · simpa using d.mixedComponentPair_first_mem τ τ' σ B pr
    · simpa using d.mixedComponentPair_second_mem τ τ' σ B pr
  invFun pos :=
    let x := (d.pairingInMixedOrder τ τ' σ).positionToPairEndpoint pos.1
    (⟨x.1, d.mixedPairComponent_positionToPairEndpoint_eq τ τ' σ B pos⟩, x.2)
  left_inv x := by
    rcases x with ⟨pr, k⟩
    have h := (d.pairingInMixedOrder τ τ' σ).pairEndpointEquiv.left_inv (pr.1, k)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change ((d.pairingInMixedOrder τ τ' σ).positionToPairEndpoint
          ((d.pairingInMixedOrder τ τ' σ).pairEndpoint (pr.1, k))).2 = k
      exact congrArg Prod.snd h
  right_inv pos := by
    apply Subtype.ext
    exact (d.pairingInMixedOrder τ τ' σ).pairEndpointEquiv.right_inv pos.1

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

/-- Transport a mixed component pair through a component-position equivalence and normalize it in a
local pairing. -/
noncomputable def TwoPointDiagram.mixedComponentPairToRestricted
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) {m : ℕ}
    (e : d.MixedComponentPosition τ τ' σ B ≃ Fin (2 * m))
    (localPairing : Pairing m) :
    d.MixedComponentPair τ τ' σ B → localPairing.NormalizedPair :=
  localPairing.normalizedPairOfEndpointEquiv (d.mixedComponentPairEndpointEquiv τ τ' σ B) e

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
  localPairing.normalizedPairEquivOfEndpointEquiv
    (d.mixedComponentPairEndpointEquiv τ τ' σ B) e
    (fun pr => by
      rw [hpartner, d.mixedRestrictedPartner_componentPairEndpoint_zero τ τ' σ B pr])

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

/-- The local normalized pair containing the transported first endpoint contains it as either its
first or second entry. -/
theorem TwoPointDiagram.mixedComponentPairToRestricted_contains_first_endpoint
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) {m : ℕ}
    (e : d.MixedComponentPosition τ τ' σ B ≃ Fin (2 * m))
    (localPairing : Pairing m) (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr).1.1 =
        e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∨
      (d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr).1.2 =
        e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) := by
  let a := e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))
  let x := localPairing.positionToPairEndpoint a
  have hx : localPairing.pairEndpoint x = a := localPairing.pairEndpointEquiv.right_inv a
  change x.1.1.1 = a ∨ x.1.1.2 = a
  rcases x with ⟨localPr, k⟩
  fin_cases k
  · left
    simpa using hx
  · right
    simpa using hx

/-- Transporting one mixed component pair to a local pairing preserves its endpoints up to swapping
their normalized order. -/
theorem TwoPointDiagram.mixedComponentPairToRestricted_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) {m : ℕ}
    (e : d.MixedComponentPosition τ τ' σ B ≃ Fin (2 * m))
    (localPairing : Pairing m)
    (hpartner : ∀ pos,
      localPairing.partner (e pos) = e (d.mixedRestrictedPartner τ τ' σ B pos))
    (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  let localPr := d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr
  have hcontains :=
    d.mixedComponentPairToRestricted_contains_first_endpoint τ τ' σ B e localPairing pr
  have hab :
      localPairing.partner (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) =
        e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := by
    rw [hpartner, d.mixedRestrictedPartner_componentPairEndpoint_zero τ τ' σ B pr]
  have hpair := (localPairing.mem_pairs_iff localPr.1.1 localPr.1.2).1 localPr.2
  rcases hcontains with hfirst | hsecond
  · left
    apply Prod.ext
    · exact hfirst
    · calc
        localPr.1.2 = localPairing.partner localPr.1.1 := hpair.2.symm
        _ = localPairing.partner
            (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by rw [hfirst]
        _ = e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := hab
  · right
    apply Prod.ext
    · have hpartnerSecond : localPairing.partner localPr.1.2 = localPr.1.1 := by
        calc
          localPairing.partner localPr.1.2 =
              localPairing.partner (localPairing.partner localPr.1.1) := by rw [hpair.2]
          _ = localPr.1.1 := localPairing.partner_partner localPr.1.1
      calc
        localPr.1.1 = localPairing.partner localPr.1.2 := hpartnerSecond.symm
        _ = localPairing.partner
            (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by rw [hsecond]
        _ = e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := hab
    · exact hsecond

/-- The generic mixed local-pairing equivalence maps each pair to its transported endpoint pair or
its swap. -/
theorem TwoPointDiagram.mixedComponentPairRestrictedEquiv_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) {m : ℕ}
    (e : d.MixedComponentPosition τ τ' σ B ≃ Fin (2 * m))
    (localPairing : Pairing m)
    (hpartner : ∀ pos,
      localPairing.partner (e pos) = e (d.mixedRestrictedPartner τ τ' σ B pos))
    (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedComponentPairRestrictedEquiv τ τ' σ B e localPairing hpartner pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairRestrictedEquiv τ τ' σ B e localPairing hpartner pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  change
    (d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairToRestricted τ τ' σ B e localPairing pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)))
  exact d.mixedComponentPairToRestricted_pair_eq_or_swap τ τ' σ B e localPairing hpartner pr

/-- Canonical external split pair transport preserves transported endpoints up to swap. -/
theorem TwoPointDiagram.mixedExternalComponentPairEquiv_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.externalComponentPart) :
    (d.mixedExternalComponentPairEquiv τ τ' σ pr).1 =
        (d.mixedExternalPositionEquiv τ τ' σ
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 0)),
          d.mixedExternalPositionEquiv τ τ' σ
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 1))) ∨
      (d.mixedExternalComponentPairEquiv τ τ' σ pr).1 =
        (d.mixedExternalPositionEquiv τ τ' σ
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 1)),
          d.mixedExternalPositionEquiv τ τ' σ
            (d.mixedComponentPairEndpointEquiv τ τ' σ d.externalComponentPart (pr, 0))) :=
  d.mixedComponentPairRestrictedEquiv_pair_eq_or_swap τ τ' σ d.externalComponentPart
    (d.mixedExternalPositionEquiv τ τ' σ) d.externalVacuumSplit.1.pairing
    (d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' σ) pr

/-- Vacuum mixed-pair restriction preserves transported endpoints up to swap. -/
theorem TwoPointDiagram.mixedVacuumComponentPairEquiv_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B) (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr).1 =
        (d.mixedVacuumPositionEquiv τ τ' σ B hVac
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)),
          d.mixedVacuumPositionEquiv τ τ' σ B hVac
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr).1 =
        (d.mixedVacuumPositionEquiv τ τ' σ B hVac
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)),
          d.mixedVacuumPositionEquiv τ τ' σ B hVac
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) :=
  d.mixedComponentPairRestrictedEquiv_pair_eq_or_swap τ τ' σ B
    (d.mixedVacuumPositionEquiv τ τ' σ B hVac)
    (d.restrictedVacuumPairing B hVac)
    (d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' σ B hVac) pr

end Common
end SecondQuantization
