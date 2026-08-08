import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderChamber
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingTimeLocality
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder

set_option linter.style.header false

/-!
# Mixed component combinatorics on fixed order chambers

Inside one `SameTwoPointOrderChamber`, the relative order of distinct mixed events is fixed.  The
relative order of atomic legs belonging to one event is fixed by that event's local leg list.  Thus
the complete mixed atomic-leg order is constant on a chamber even though the actual interaction
times may vary.

This module lifts that statement through the existing component position and normalized-pair time
transports.  In particular, pair normalization cannot swap endpoints inside one chamber, and the
component-internal fermionic crossing relation is preserved without requiring `ComponentTimeEq`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- The complete mixed atomic-leg order is constant inside one mixed-event order chamber.  Distinct
event blocks use chamber invariance of event positions; legs in one event block use the fixed local
leg order. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ x <
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  by_cases hxy : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y
  · let event := orderedTwoPointLegEvent x
    have hx : x ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event] using orderedTwoPointLeg_mem_eventAtomicLegs x
    have hy : y ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedTwoPointLeg_mem_eventAtomicLegs y
    have hσ := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' σ) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ event) hx hy
    have hυ := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' υ) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' υ)
      (orderedTwoPointTimedEvents_all_mem τ τ' υ event) hx hy
    calc
      mixedTimeOrderedAtomicLegPosition τ τ' σ x <
          mixedTimeOrderedAtomicLegPosition τ τ' σ y ↔
        (twoPointTimedEventAtomicLegs event).idxOf x <
          (twoPointTimedEventAtomicLegs event).idxOf y := by
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
              mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using hσ
      _ ↔ mixedTimeOrderedAtomicLegPosition τ τ' υ x <
          mixedTimeOrderedAtomicLegPosition τ τ' υ y := by
            symm
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
              mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using hυ
  · rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' σ x y hxy,
      mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' υ x y hxy]
    exact orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber
      hChamber (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y)

/-- Canonical transport of positions belonging to one full component preserves strict mixed order
throughout one order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
  let x := mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1
  let y := mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1
  have hOrder := mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber
    τ τ' σ υ x y hChamber
  have hpSource : mixedTimeOrderedAtomicLegPosition τ τ' σ x = p.1 := by
    dsimp [x]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hqSource : mixedTimeOrderedAtomicLegPosition τ τ' σ y = q.1 := by
    dsimp [y]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hpTarget :
      mixedTimeOrderedAtomicLegPosition τ τ' υ x =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 := by
    change mixedTimeOrderedAtomicLegPosition τ τ' υ
      (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) = _
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hqTarget :
      mixedTimeOrderedAtomicLegPosition τ τ' υ y =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
    change mixedTimeOrderedAtomicLegPosition τ τ' υ
      (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1) = _
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B q]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  rw [hpSource, hqSource, hpTarget, hqTarget] at hOrder
  exact hOrder

/-- Inside one order chamber, canonical pair-time transport preserves the normalized endpoint order
exactly; the swap alternative cannot occur even though the component interaction times may change. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
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
    simpa [q] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_or_swap τ τ' σ υ B pr
  rcases hCases with hSame | hSwap
  · exact hSame
  · have hSource :
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff
        pr.1.1.1 pr.1.1.2).mp pr.1.2 |>.1
    have hTransport :=
      (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
        τ τ' σ υ B hChamber
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))).1 hSource
    have hTarget :
        (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' υ).mem_pairs_iff
        q.1.1.1 q.1.1.2).mp q.1.2 |>.1
    rw [hSwap.1, hSwap.2] at hTarget
    exact (lt_asymm hTarget hTransport).elim

/-- Canonical component pair transport preserves and reflects every component-internal crossing
inside one mixed-event order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingPreserving_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B := by
  classical
  intro p q
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
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
        τ τ' σ υ B hChamber p
  have hqEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (tq, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (tq, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1 := by
    simpa [tq, q0, q1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
        τ τ' σ υ B hChamber q
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
  have h00 := d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
    τ τ' σ υ B hChamber p0 q0
  have h01 := d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
    τ τ' σ υ B hChamber q0 p1
  have h11 := d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
    τ τ' σ υ B hChamber p1 q1
  unfold Crosses
  constructor
  · rintro ⟨hpq, hqp, hpq'⟩
    have ht00 := h00.mp (by simpa [p0, q0] using hpq)
    have ht01 := h01.mp (by simpa [q0, p1] using hqp)
    have ht11 := h11.mp (by simpa [p1, q1] using hpq')
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
    · simpa [p0, q0] using h00.mpr ht00
    · simpa [q0, p1] using h01.mpr ht01
    · simpa [p1, q1] using h11.mpr ht11

/-- The number of component-internal crossings is constant on one mixed-event order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B :=
  d.mixedComponentCrossingCount_eq_of_timeTransport τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber
      τ τ' σ υ B hChamber)

/-- The exchange-statistics weight of one component is constant on one mixed-event order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B :=
  d.mixedComponentWeight_eq_of_timeTransport s τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber
      τ τ' σ υ B hChamber)

end Fermionic
end SecondQuantization
