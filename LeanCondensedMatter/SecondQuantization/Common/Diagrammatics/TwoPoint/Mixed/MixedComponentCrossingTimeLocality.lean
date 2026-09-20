import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber

set_option linter.style.header false

/-!
# Component-locality of mixed pair crossings and order chambers

Canonical component pair transport preserves normalized endpoints when component position order is
preserved. Endpoint bookkeeping and crossing-count reindexing are proof-local to this module; the
public API exposes endpoint-leg and exchange-weight locality inside fixed mixed-order chambers.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Canonical comparison of mixed positions of one full component across interaction-time
assignments, used only to prove chamber locality. -/
private noncomputable def TwoPointDiagram.mixedComponentPositionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

/-- Time transport preserves the atomic leg represented by a mixed component position. -/
private theorem TwoPointDiagram.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeOrderedAtomicLegEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 := by
  rw [← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  apply congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
  have h := congrArg Subtype.val
    (show d.mixedComponentPositionEquiv τ τ' υ B
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
        d.mixedComponentPositionEquiv τ τ' σ B p by
      simp [TwoPointDiagram.mixedComponentPositionTimeEquiv])
  change mixedTimeAmbientPositionEquiv τ τ' υ
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
    mixedTimeAmbientPositionEquiv τ τ' σ p.1 at h
  exact h

/-- Component position transport preserves strict order inside one mixed-order chamber. -/
private theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
  have hOrder :
      (mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) <
        mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) <
        mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)) :=
    mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff τ τ' σ υ _ _
      (orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber
        hChamber
        (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1))
        (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)))
  have hpSource :
      mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) = p.1 :=
    mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hqSource :
      mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1) = q.1 :=
    mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hpTarget :
      mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 := by
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hqTarget :
      mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1) =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B q]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  rw [hpSource, hqSource, hpTarget, hqTarget] at hOrder
  exact hOrder

@[simp]
private theorem TwoPointDiagram.mixedExternalComponentPairEquiv_pairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.externalComponentPart) :
    d.mixedExternalComponentPairEquiv τ τ' υ
        (d.mixedComponentPairTimeEquiv τ τ' σ υ d.externalComponentPart pr) =
      d.mixedExternalComponentPairEquiv τ τ' σ pr := by
  simp [TwoPointDiagram.mixedComponentPairTimeEquiv]

@[simp]
private theorem TwoPointDiagram.mixedVacuumComponentPairEquiv_pairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedVacuumComponentPairEquiv τ τ' υ B hVac
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr) =
      d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
  have hB : B ≠ d.externalComponentPart :=
    (d.componentIsVacuum_iff_ne_externalComponentPart B).1 hVac
  simp [TwoPointDiagram.mixedComponentPairTimeEquiv, hB]

private theorem TwoPointDiagram.mixedComponentPairEndpoints_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) {m : ℕ}
    (e : d.MixedComponentPosition τ τ' σ B ≃ Fin (2 * m))
    (localPairing : Pairing m)
    (hpartner : ∀ pos,
      localPairing.partner (e pos) = e (d.mixedRestrictedPartner τ τ' σ B pos))
    (pr : d.MixedComponentPair τ τ' σ B) :
    (localPairing.normalizedPairOfEndpointEquiv
        (d.mixedComponentPairEndpointEquiv τ τ' σ B) e pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (localPairing.normalizedPairOfEndpointEquiv
        (d.mixedComponentPairEndpointEquiv τ τ' σ B) e pr).1 =
        (e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)),
          e (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  apply localPairing.normalizedPairOfEndpointEquiv_pair_eq_or_swap
  intro q
  rw [hpartner, d.mixedRestrictedPartner_componentPairEndpoint_zero τ τ' σ B q]

@[simp]
private theorem TwoPointDiagram.mixedExternalPositionEquiv_positionTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (p : d.MixedComponentPosition τ τ' σ d.externalComponentPart) :
    d.mixedExternalPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.externalComponentPart p) =
      d.mixedExternalPositionEquiv τ τ' σ p := by
  change d.externalComponentLegEquiv.symm
      (d.mixedComponentPositionEquiv τ τ' υ d.externalComponentPart
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.externalComponentPart p)) =
    d.externalComponentLegEquiv.symm
      (d.mixedComponentPositionEquiv τ τ' σ d.externalComponentPart p)
  simp [TwoPointDiagram.mixedComponentPositionTimeEquiv]

@[simp]
private theorem TwoPointDiagram.mixedVacuumPositionEquiv_positionTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedVacuumPositionEquiv τ τ' υ B hVac
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedVacuumPositionEquiv τ τ' σ B hVac p := by
  simp [TwoPointDiagram.mixedVacuumPositionEquiv,
    TwoPointDiagram.mixedComponentPositionTimeEquiv]

private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  classical
  dsimp only
  by_cases hB : B = d.externalComponentPart
  · subst B
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ d.externalComponentPart pr
    have hlocal :
        d.mixedExternalComponentPairEquiv τ τ' υ q =
          d.mixedExternalComponentPairEquiv τ τ' σ pr := by
      simpa [q] using d.mixedExternalComponentPairEquiv_pairTimeEquiv τ τ' σ υ pr
    have hlocalVal :
        (d.mixedExternalComponentPairEquiv τ τ' υ q).1 =
          (d.mixedExternalComponentPairEquiv τ τ' σ pr).1 :=
      congrArg Subtype.val hlocal
    rcases d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' σ
        d.externalComponentPart (d.mixedExternalPositionEquiv τ τ' σ)
        d.externalVacuumSplit.1.pairing
        (d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' σ) pr with hp | hp <;>
      rcases d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' υ
          d.externalComponentPart (d.mixedExternalPositionEquiv τ τ' υ)
          d.externalVacuumSplit.1.pairing
          (d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' υ) q with hq | hq
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
  · have hVac : d.ComponentIsVacuum B :=
      (d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    have hlocal :
        d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q =
          d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
      simpa [q] using d.mixedVacuumComponentPairEquiv_pairTimeEquiv τ τ' σ υ B hVac pr
    have hlocalVal :
        (d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q).1 =
          (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr).1 :=
      congrArg Subtype.val hlocal
    rcases d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' σ B
        (d.mixedVacuumPositionEquiv τ τ' σ B hVac)
        (d.restrictedVacuumPairing B hVac)
        (d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' σ B hVac) pr
      with hp | hp <;>
      rcases d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' υ B
          (d.mixedVacuumPositionEquiv τ τ' υ B hVac)
          (d.restrictedVacuumPairing B hVac)
          (d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' υ B hVac) q
        with hq | hq
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords

private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  change d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) = _ ∧
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) = _
  have hCases :
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
    simpa [q] using d.mixedComponentPairTimeEquiv_endpoints_eq_or_swap τ τ' σ υ B pr
  rcases hCases with hSame | hSwap
  · exact hSame
  · have hSource :
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1.1 pr.1.1.2).mp pr.1.2 |>.1
    have hTransport :=
      (hOrder (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))).1 hSource
    have hTarget :
        (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' υ).mem_pairs_iff q.1.1.1 q.1.1.2).mp q.1.2 |>.1
    rw [hSwap.1, hSwap.2] at hTarget
    exact (lt_asymm hTarget hTransport).elim

private theorem TwoPointDiagram.mixedComponentCrosses_iff_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1)
    (p q : d.MixedComponentPair τ τ' σ B) :
    Crosses p.1.1 q.1.1 ↔
      Crosses
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B p).1.1
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B q).1.1 := by
  classical
  let tp := d.mixedComponentPairTimeEquiv τ τ' σ υ B p
  let tq := d.mixedComponentPairTimeEquiv τ τ' σ υ B q
  let p0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (p, 0)
  let p1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (p, 1)
  let q0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (q, 0)
  let q1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (q, 1)
  have endpointVal (ρ : Fin n → ℝ) (r : d.MixedComponentPair τ τ' ρ B) (k : Fin 2) :
      (d.mixedComponentPairEndpointEquiv τ τ' ρ B (r, k)).1 =
        (d.pairingInMixedOrder τ τ' ρ).pairEndpoint (r.1, k) := by
    unfold TwoPointDiagram.mixedComponentPairEndpointEquiv
    exact Pairing.normalizedPairSubtypeEndpointEquiv_apply_val
      (d.pairingInMixedOrder τ τ' ρ)
      (fun x => d.mixedPositionComponent τ τ' ρ x = B) _ r k
  have hpEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (tp, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (tp, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1 := by
    simpa [tp, p0, p1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B hOrder p
  have hqEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (tq, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (tq, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1 := by
    simpa [tq, q0, q1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B hOrder q
  have hp0Val :
      tp.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 := by
    simpa [tp, endpointVal] using congrArg Subtype.val hpEnds.1
  have hp1Val :
      tp.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [tp, endpointVal] using congrArg Subtype.val hpEnds.2
  have hq0Val :
      tq.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 := by
    simpa [tq, endpointVal] using congrArg Subtype.val hqEnds.1
  have hq1Val :
      tq.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1).1 := by
    simpa [tq, endpointVal] using congrArg Subtype.val hqEnds.2
  have h00 := hOrder p0 q0
  have h01 := hOrder q0 p1
  have h11 := hOrder p1 q1
  unfold Crosses
  constructor
  · rintro ⟨hpq, hqp, hpq'⟩
    have ht00 := h00.mp (by simpa [p0, q0, endpointVal] using hpq)
    have ht01 := h01.mp (by simpa [q0, p1, endpointVal] using hqp)
    have ht11 := h11.mp (by simpa [p1, q1, endpointVal] using hpq')
    refine ⟨?_, ?_, ?_⟩
    · rw [hp0Val, hq0Val]
      exact ht00
    · rw [hq0Val, hp1Val]
      exact ht01
    · rw [hp1Val, hq1Val]
      exact ht11
  · rintro ⟨hpq, hqp, hpq'⟩
    have ht00 :
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 := by
      rw [← hp0Val, ← hq0Val]
      exact hpq
    have ht01 :
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
      rw [← hq0Val, ← hp1Val]
      exact hqp
    have ht11 :
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1).1 := by
      rw [← hp1Val, ← hq1Val]
      exact hpq'
    refine ⟨?_, ?_, ?_⟩
    · simpa [p0, q0, endpointVal] using h00.mpr ht00
    · simpa [q0, p1, endpointVal] using h01.mpr ht01
    · simpa [p1, q1, endpointVal] using h11.mpr ht11

private theorem TwoPointDiagram.mixedComponentCrossingCount_eq_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B := by
  classical
  unfold TwoPointDiagram.mixedComponentCrossingCount
    TwoPointDiagram.mixedComponentOrientedCrossingCount
  simp only [Pairing.componentCrossingCount, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv
    (fun p : d.MixedComponentPair τ τ' σ B => p.1.1)
    (fun p : d.MixedComponentPair τ τ' υ B => p.1.1)
    (d.mixedComponentPairTimeEquiv τ τ' σ υ B)
    (fun p q =>
      d.mixedComponentCrosses_iff_of_positionOrder τ τ' σ υ B hOrder p q)

/-- Inside one order chamber, canonical transport of a normalized component pair preserves the two
underlying standard atomic legs in their normalized order. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.1 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.1 ∧
      mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.2 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.2 := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  let p0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)
  let p1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)
  have endpointVal (ρ : Fin n → ℝ) (r : d.MixedComponentPair τ τ' ρ B) (k : Fin 2) :
      (d.mixedComponentPairEndpointEquiv τ τ' ρ B (r, k)).1 =
        (d.pairingInMixedOrder τ τ' ρ).pairEndpoint (r.1, k) := by
    unfold TwoPointDiagram.mixedComponentPairEndpointEquiv
    exact Pairing.normalizedPairSubtypeEndpointEquiv_apply_val
      (d.pairingInMixedOrder τ τ' ρ)
      (fun x => d.mixedPositionComponent τ τ' ρ x = B) _ r k
  have hEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1 := by
    simpa [q, p0, p1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B
        (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
          τ τ' σ υ B hChamber) pr
  have h0Pos :
      q.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 := by
    simpa [q, endpointVal] using congrArg Subtype.val hEnds.1
  have h1Pos :
      q.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [q, endpointVal] using congrArg Subtype.val hEnds.2
  constructor
  · rw [h0Pos]
    simpa [p0, endpointVal] using
      d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p0
  · rw [h1Pos]
    simpa [p1, endpointVal] using
      d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p1

/-- Component exchange-statistics weight is constant on one chamber. -/
theorem TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B := by
  unfold TwoPointDiagram.mixedComponentWeight
  rw [d.mixedComponentCrossingCount_eq_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
      τ τ' σ υ B hChamber)]

end Common
end SecondQuantization
