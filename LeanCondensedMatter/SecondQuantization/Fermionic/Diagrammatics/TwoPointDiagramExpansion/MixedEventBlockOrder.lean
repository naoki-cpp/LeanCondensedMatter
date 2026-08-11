import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder

set_option linter.style.header false

/-!
# Ordering inside mixed-time atomic event blocks

The mixed atomic list is a `flatMap` of event-local atomic-leg lists. Thus all legs contributed by
one external or interaction event form one contiguous block. This module records both consequences
needed by component locality:

- positions inside one event block are ordered only by that event's local leg list;
- positions in distinct event blocks are ordered only by the relative order of those two events.

Consequently the relative mixed position of two standard two-point legs depends only on the times of
their two supporting events and on their fixed event-local leg coordinates.
-/

namespace SecondQuantization
namespace Fermionic

/-- The mixed event supporting one standard two-point leg. -/
def orderedTwoPointLegEvent {n : ℕ} : OrderedTwoPointLeg n → TwoPointTimedEvent n
  | .inl e => .inl e
  | .inr p => .inr p.1.1

/-- Every standard two-point leg belongs to the local leg list of its supporting event. -/
theorem orderedTwoPointLeg_mem_eventAtomicLegs {n : ℕ} (leg : OrderedTwoPointLeg n) :
    leg ∈ twoPointTimedEventAtomicLegs (orderedTwoPointLegEvent leg) := by
  cases leg with
  | inl e => simp [orderedTwoPointLegEvent]
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      fin_cases l <;> simp [orderedTwoPointLegEvent, twoPointTimedEventAtomicLegs]

/-- The mixed position occupied by a standard two-point leg identity. -/
noncomputable def mixedTimeOrderedAtomicLegPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    Fin (2 * (2 * n + 1)) :=
  (mixedTimeOrderedAtomicLegEquiv τ τ' σ).symm leg

/-- Legs in one mixed-time event block have identical comparison with every leg outside that block. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_uniform {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) (x y z : OrderedTwoPointLeg n)
    (hEvent : event ∈ orderedTwoPointTimedEvents τ τ' σ)
    (hx : x ∈ twoPointTimedEventAtomicLegs event)
    (hy : y ∈ twoPointTimedEventAtomicLegs event)
    (hz : z ∈ mixedTimeOrderedAtomicLegs τ τ' σ)
    (hzOutside : z ∉ twoPointTimedEventAtomicLegs event) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ z) =
      (mixedTimeOrderedAtomicLegPosition τ τ' σ y <
        mixedTimeOrderedAtomicLegPosition τ τ' σ z) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  have h := List.idxOf_flatMap_block_lt_uniform twoPointTimedEventAtomicLegs
    (orderedTwoPointTimedEvents τ τ' σ) event x y z
    (mixedTimeOrderedAtomicLegs_nodup τ τ' σ) hEvent hx hy hz hzOutside
  simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
    mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using h

private theorem mixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hEvent : orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x) <
      orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) :
    mixedTimeOrderedAtomicLegPosition τ τ' σ x <
      mixedTimeOrderedAtomicLegPosition τ τ' σ y := by
  classical
  letI : BEq (TwoPointTimedEvent n) := instBEqOfDecidableEq
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  have hEventIdx :
      (orderedTwoPointTimedEvents τ τ' σ).idxOf (orderedTwoPointLegEvent x) <
        (orderedTwoPointTimedEvents τ τ' σ).idxOf (orderedTwoPointLegEvent y) := by
    simpa [orderedTwoPointTimedEventPosition, orderedTwoPointTimedEventEquiv,
      List.Nodup.getEquivOfForallMemList] using hEvent
  have h := List.idxOf_flatMap_lt_of_idxOf_lt twoPointTimedEventAtomicLegs
    (orderedTwoPointTimedEvents τ τ' σ)
    (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y) x y
    (orderedTwoPointTimedEvents_nodup τ τ' σ)
    (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
    (orderedTwoPointTimedEvents_all_mem τ τ' σ (orderedTwoPointLegEvent x))
    (orderedTwoPointTimedEvents_all_mem τ τ' σ (orderedTwoPointLegEvent y))
    (orderedTwoPointLeg_mem_eventAtomicLegs x)
    (orderedTwoPointLeg_mem_eventAtomicLegs y) hEventIdx
  simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
    mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using h

/-- For legs supported on distinct events, flattened atomic-leg order is exactly event order. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hxy : orderedTwoPointLegEvent x ≠ orderedTwoPointLegEvent y) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x) <
        orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) := by
  constructor
  · intro hLeg
    rcases lt_trichotomy
        (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x))
        (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) with
      hEvent | hEvent | hEvent
    · exact hEvent
    · exact (hxy ((orderedTwoPointTimedEventEquiv τ τ' σ).symm.injective hEvent)).elim
    · have hReverse :=
        mixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt τ τ' σ y x hEvent
      exact (lt_asymm hLeg hReverse).elim
  · exact mixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt τ τ' σ x y

/-- The flattened atomic-leg order of two legs is determined by the relative order of their two
supporting events: legs sharing one event are ordered by that event's fixed local leg list, and legs
on distinct events follow the event order supplied by `hEvent`. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hEvent :
      (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x) <
          orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) ↔
        (orderedTwoPointTimedEventPosition τ τ' υ (orderedTwoPointLegEvent x) <
          orderedTwoPointTimedEventPosition τ τ' υ (orderedTwoPointLegEvent y))) :
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
    exact hEvent

/-- The relative flattened positions of two standard legs depend only on the times of their two
supporting events and on their fixed local leg coordinates. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventTime_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hxTime : twoPointTimedEventTime τ τ' σ (orderedTwoPointLegEvent x) =
      twoPointTimedEventTime τ τ' υ (orderedTwoPointLegEvent x))
    (hyTime : twoPointTimedEventTime τ τ' σ (orderedTwoPointLegEvent y) =
      twoPointTimedEventTime τ τ' υ (orderedTwoPointLegEvent y)) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ x <
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) :=
  mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff τ τ' σ υ x y
    (orderedTwoPointTimedEventPosition_lt_iff_of_eventTime_eq
      τ τ' σ υ (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y) hxTime hyTime)

end Fermionic
end SecondQuantization
