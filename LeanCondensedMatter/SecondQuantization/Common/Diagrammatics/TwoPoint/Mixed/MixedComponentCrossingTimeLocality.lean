import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber

set_option linter.style.header false

/-!
# Component-locality of mixed pair crossings and order chambers

Canonical transport of component-local normalized pairs preserves their endpoint legs whenever the
component-position order is preserved. Consequently both endpoint data and exchange weights are
invariant under transport within a fixed mixed-order chamber.

These statements depend only on the mixed ordering, component decomposition, and pairing geometry.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Canonical comparison of mixed positions of one full component across interaction-time
assignments, used only to prove chamber locality. -/
private noncomputable def TwoPointDiagram.mixedComponentPositionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

/-- Time transport preserves the atomic leg represented by a mixed component position. -/
private theorem TwoPointDiagram.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
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
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
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

private theorem TwoPointDiagram.mixedComponentPairEndpoints_pair_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) {m : ℕ}
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

/-- Identifying the same local normalized pair at two position coordinate systems preserves
its unordered endpoints. Any difference is solely the normalization orientation. -/
private theorem pairEndpoints_eq_or_swap_of_equiv
    {P Q R : Type*} (e : P ≃ R) (e' : Q ≃ R) (f : P ≃ Q)
    (htransport : ∀ x, e' (f x) = e x)
    {x₀ x₁ : P} {y₀ y₁ : Q} {s t : R × R}
    (hpair : t = s)
    (hp : s = (e x₀, e x₁) ∨ s = (e x₁, e x₀))
    (hq : t = (e' y₀, e' y₁) ∨ t = (e' y₁, e' y₀)) :
    (y₀ = f x₀ ∧ y₁ = f x₁) ∨ (y₀ = f x₁ ∧ y₁ = f x₀) := by
  have recover {a b : P} {c d : Q}
      (h : (e' c, e' d) = (e a, e b)) :
      c = f a ∧ d = f b := by
    constructor
    · apply e'.injective
      simpa only [htransport] using congrArg Prod.fst h
    · apply e'.injective
      simpa only [htransport] using congrArg Prod.snd h
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact Or.inl (recover (hq.symm.trans (hpair.trans hp)))
  · obtain ⟨h1, h0⟩ := recover (hq.symm.trans (hpair.trans hp))
    exact Or.inr ⟨h0, h1⟩
  · exact Or.inr (recover (hq.symm.trans (hpair.trans hp)))
  · obtain ⟨h1, h0⟩ := recover (hq.symm.trans (hpair.trans hp))
    exact Or.inl ⟨h0, h1⟩

private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
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
      simpa [q, TwoPointDiagram.mixedComponentPairTimeEquiv]
    have hp := d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' σ
      d.externalComponentPart (d.mixedExternalPositionEquiv τ τ' σ)
      d.externalVacuumSplit.1.pairing
      (d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' σ) pr
    have hq := d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' υ
      d.externalComponentPart (d.mixedExternalPositionEquiv τ τ' υ)
      d.externalVacuumSplit.1.pairing
      (d.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv τ τ' υ) q
    exact pairEndpoints_eq_or_swap_of_equiv
      (d.mixedExternalPositionEquiv τ τ' σ)
      (d.mixedExternalPositionEquiv τ τ' υ)
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.externalComponentPart)
      (fun p => by
        change d.externalComponentLegEquiv.symm
            (d.mixedComponentPositionEquiv τ τ' υ d.externalComponentPart
              (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.externalComponentPart p)) =
          d.externalComponentLegEquiv.symm
            (d.mixedComponentPositionEquiv τ τ' σ d.externalComponentPart p)
        simp [TwoPointDiagram.mixedComponentPositionTimeEquiv])
      (congrArg Subtype.val hlocal) hp hq
  · have hVac : ComponentIsVacuum (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) :=
      (d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    have hlocal :
        d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q =
          d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
      simpa [q, TwoPointDiagram.mixedComponentPairTimeEquiv, hB]
    have hp := d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' σ B
      (d.mixedVacuumPositionEquiv τ τ' σ B hVac)
      (d.restrictedVacuumPairing B hVac)
      (d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' σ B hVac) pr
    have hq := d.mixedComponentPairEndpoints_pair_eq_or_swap τ τ' υ B
      (d.mixedVacuumPositionEquiv τ τ' υ B hVac)
      (d.restrictedVacuumPairing B hVac)
      (d.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv τ τ' υ B hVac) q
    exact pairEndpoints_eq_or_swap_of_equiv
      (d.mixedVacuumPositionEquiv τ τ' σ B hVac)
      (d.mixedVacuumPositionEquiv τ τ' υ B hVac)
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B)
      (fun p => by
        simp [TwoPointDiagram.mixedVacuumPositionEquiv,
          TwoPointDiagram.mixedComponentPositionTimeEquiv])
      (congrArg Subtype.val hlocal) hp hq

private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
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
  rcases d.mixedComponentPairTimeEquiv_endpoints_eq_or_swap τ τ' σ υ B pr with
    hSame | hSwap
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
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
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
    simpa [tp] using congrArg Subtype.val hpEnds.1
  have hp1Val :
      tp.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [tp] using congrArg Subtype.val hpEnds.2
  have hq0Val :
      tq.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 := by
    simpa [tq] using congrArg Subtype.val hqEnds.1
  have hq1Val :
      tq.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1).1 := by
    simpa [tq] using congrArg Subtype.val hqEnds.2
  have hCross := and_congr (hOrder p0 q0)
    (and_congr (hOrder q0 p1) (hOrder p1 q1))
  rw [← hp0Val, ← hq0Val, ← hp1Val, ← hq1Val] at hCross
  simpa [Crosses, p0, p1, q0, q1] using hCross

/-- Inside one order chamber, canonical transport of a normalized component pair preserves the two
underlying standard atomic legs in their normalized order. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
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
    simpa [q] using congrArg Subtype.val hEnds.1
  have h1Pos :
      q.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [q] using congrArg Subtype.val hEnds.2
  constructor
  · rw [h0Pos]
    simpa [p0] using
      d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p0
  · rw [h1Pos]
    simpa [p1] using
      d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p1

/-- Component exchange-statistics weight is constant on one chamber. -/
theorem TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B := by
  unfold TwoPointDiagram.mixedComponentWeight
  congr 1
  unfold TwoPointDiagram.mixedComponentCrossingCount
  unfold TwoPointDiagram.mixedComponentOrientedCrossingCount
  simp only [Pairing.componentCrossingCount, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv
    (fun p : d.MixedComponentPair τ τ' σ B => p.1.1)
    (fun p : d.MixedComponentPair τ τ' υ B => p.1.1)
    (d.mixedComponentPairTimeEquiv τ τ' σ υ B)
    (fun p q =>
      d.mixedComponentCrosses_iff_of_positionOrder τ τ' σ υ B
        (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
          τ τ' σ υ B hChamber) p q)

end Common
end SecondQuantization
