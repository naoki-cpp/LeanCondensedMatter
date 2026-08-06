import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing

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

/-- In a duplicate-free flattened list, two elements of one block have the same order relation to an
element outside that block. -/
private theorem idxOf_flatMap_block_lt_uniform
    {α β : Type*} [DecidableEq β] (f : α → List β)
    (events : List α) (event : α) (x y z : β)
    (hNodup : (events.flatMap f).Nodup)
    (hEvent : event ∈ events) (hx : x ∈ f event) (hy : y ∈ f event)
    (hz : z ∈ events.flatMap f) (hzOutside : z ∉ f event) :
    ((events.flatMap f).idxOf x < (events.flatMap f).idxOf z) =
      ((events.flatMap f).idxOf y < (events.flatMap f).idxOf z) := by
  induction events generalizing event x y z with
  | nil => simp at hEvent
  | cons a events ih =>
      simp only [List.flatMap_cons] at hNodup hz ⊢
      have hNodupTail : (events.flatMap f).Nodup := hNodup.of_append_right
      have hDisjoint : List.Disjoint (f a) (events.flatMap f) := hNodup.disjoint
      rw [List.mem_cons] at hEvent
      rcases hEvent with rfl | hEvent
      · have hzTail : z ∈ events.flatMap f := by
          rw [List.mem_append] at hz
          exact hz.resolve_left hzOutside
        have hxLt : (f event).idxOf x < (f event).length :=
          List.idxOf_lt_length_of_mem hx
        have hyLt : (f event).idxOf y < (f event).length :=
          List.idxOf_lt_length_of_mem hy
        rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_mem hy,
          List.idxOf_append_of_notMem hzOutside]
        have hxBefore :
            (f event).idxOf x < (f event).length + (events.flatMap f).idxOf z := by
          omega
        have hyBefore :
            (f event).idxOf y < (f event).length + (events.flatMap f).idxOf z := by
          omega
        simp [hxBefore, hyBefore]
      · have hxTail : x ∈ events.flatMap f := by
          rw [List.mem_flatMap]
          exact ⟨event, hEvent, hx⟩
        have hyTail : y ∈ events.flatMap f := by
          rw [List.mem_flatMap]
          exact ⟨event, hEvent, hy⟩
        have hxNotHead : x ∉ f a := by
          intro hxa
          exact (List.disjoint_left.1 hDisjoint) hxa hxTail
        have hyNotHead : y ∉ f a := by
          intro hya
          exact (List.disjoint_left.1 hDisjoint) hya hyTail
        rw [List.mem_append] at hz
        rcases hz with hzHead | hzTail
        · have hzLt : (f a).idxOf z < (f a).length :=
            List.idxOf_lt_length_of_mem hzHead
          rw [List.idxOf_append_of_notMem hxNotHead,
            List.idxOf_append_of_notMem hyNotHead,
            List.idxOf_append_of_mem hzHead]
          have hxNotBefore :
              ¬ (f a).length + (events.flatMap f).idxOf x < (f a).idxOf z := by
            omega
          have hyNotBefore :
              ¬ (f a).length + (events.flatMap f).idxOf y < (f a).idxOf z := by
            omega
          simp [hxNotBefore, hyNotBefore]
        · have hzNotHead : z ∉ f a := by
            intro hza
            exact (List.disjoint_left.1 hDisjoint) hza hzTail
          rw [List.idxOf_append_of_notMem hxNotHead,
            List.idxOf_append_of_notMem hyNotHead,
            List.idxOf_append_of_notMem hzNotHead]
          simpa only [Nat.add_lt_add_iff_left] using
            ih (event := event) (x := x) (y := y) (z := z)
              hNodupTail hEvent hx hy hzTail hzOutside

/-- Inside one block of a duplicate-free flattened list, global order is exactly local block order. -/
private theorem idxOf_flatMap_block_lt_iff
    {α β : Type*} [DecidableEq β] (f : α → List β)
    (events : List α) (event : α) (x y : β)
    (hNodup : (events.flatMap f).Nodup)
    (hEvent : event ∈ events) (hx : x ∈ f event) (hy : y ∈ f event) :
    (events.flatMap f).idxOf x < (events.flatMap f).idxOf y ↔
      (f event).idxOf x < (f event).idxOf y := by
  induction events generalizing event x y with
  | nil => simp at hEvent
  | cons a events ih =>
      simp only [List.flatMap_cons] at hNodup ⊢
      have hNodupTail : (events.flatMap f).Nodup := hNodup.of_append_right
      have hDisjoint : List.Disjoint (f a) (events.flatMap f) := hNodup.disjoint
      rw [List.mem_cons] at hEvent
      rcases hEvent with rfl | hEvent
      · rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_mem hy]
      · have hxTail : x ∈ events.flatMap f := by
          rw [List.mem_flatMap]
          exact ⟨event, hEvent, hx⟩
        have hyTail : y ∈ events.flatMap f := by
          rw [List.mem_flatMap]
          exact ⟨event, hEvent, hy⟩
        have hxNotHead : x ∉ f a := by
          intro hxa
          exact (List.disjoint_left.1 hDisjoint) hxa hxTail
        have hyNotHead : y ∉ f a := by
          intro hya
          exact (List.disjoint_left.1 hDisjoint) hya hyTail
        rw [List.idxOf_append_of_notMem hxNotHead,
          List.idxOf_append_of_notMem hyNotHead]
        simpa only [Nat.add_lt_add_iff_left] using
          ih (event := event) (x := x) (y := y) hNodupTail hEvent hx hy

/-- If one event occurs before another in a duplicate-free event list, every leg in the first event
block occurs before every leg in the second block of the duplicate-free flattened list. -/
private theorem idxOf_flatMap_lt_of_event_idxOf_lt
    {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → List β)
    (events : List α) (a b : α) (x y : β)
    (hEventsNodup : events.Nodup) (hFlatNodup : (events.flatMap f).Nodup)
    (ha : a ∈ events) (hb : b ∈ events) (hx : x ∈ f a) (hy : y ∈ f b)
    (hab : events.idxOf a < events.idxOf b) :
    (events.flatMap f).idxOf x < (events.flatMap f).idxOf y := by
  induction events generalizing a b x y with
  | nil => simp at ha
  | cons c events ih =>
      have hcNotMem : c ∉ events := (List.nodup_cons.1 hEventsNodup).1
      have hEventsNodupTail : events.Nodup := (List.nodup_cons.1 hEventsNodup).2
      simp only [List.flatMap_cons] at hFlatNodup ⊢
      have hFlatNodupTail : (events.flatMap f).Nodup := hFlatNodup.of_append_right
      have hDisjoint : List.Disjoint (f c) (events.flatMap f) := hFlatNodup.disjoint
      rw [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (lt_irrefl _ hab).elim
        · have hyTail : y ∈ events.flatMap f := by
            rw [List.mem_flatMap]
            exact ⟨b, hb, hy⟩
          have hyNotHead : y ∉ f c := by
            intro hyc
            exact (List.disjoint_left.1 hDisjoint) hyc hyTail
          rw [List.idxOf_append_of_mem hx,
            List.idxOf_append_of_notMem hyNotHead]
          have hxLt : (f c).idxOf x < (f c).length :=
            List.idxOf_lt_length_of_mem hx
          omega
      · rcases hb with rfl | hb
        · have hca : c ≠ a := by
            intro hca
            subst a
            exact hcNotMem ha
          rw [List.idxOf_cons_ne events hca, List.idxOf_cons_self] at hab
          omega
        · have hca : c ≠ a := by
            intro hca
            subst a
            exact hcNotMem ha
          have hcb : c ≠ b := by
            intro hcb
            subst b
            exact hcNotMem hb
          have habTail : events.idxOf a < events.idxOf b := by
            simpa [List.idxOf_cons_ne events hca,
              List.idxOf_cons_ne events hcb] using hab
          have hxTail : x ∈ events.flatMap f := by
            rw [List.mem_flatMap]
            exact ⟨a, ha, hx⟩
          have hyTail : y ∈ events.flatMap f := by
            rw [List.mem_flatMap]
            exact ⟨b, hb, hy⟩
          have hxNotHead : x ∉ f c := by
            intro hxc
            exact (List.disjoint_left.1 hDisjoint) hxc hxTail
          have hyNotHead : y ∉ f c := by
            intro hyc
            exact (List.disjoint_left.1 hDisjoint) hyc hyTail
          rw [List.idxOf_append_of_notMem hxNotHead,
            List.idxOf_append_of_notMem hyNotHead]
          simpa only [Nat.add_lt_add_iff_left] using
            ih (a := a) (b := b) (x := x) (y := y)
              hEventsNodupTail hFlatNodupTail ha hb hx hy habTail

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
      simp [orderedTwoPointLegEvent, twoPointTimedEventAtomicLegs]

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
  have h := idxOf_flatMap_block_lt_uniform twoPointTimedEventAtomicLegs
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
  have hEventIdx :
      (orderedTwoPointTimedEvents τ τ' σ).idxOf (orderedTwoPointLegEvent x) <
        (orderedTwoPointTimedEvents τ τ' σ).idxOf (orderedTwoPointLegEvent y) := by
    simpa [orderedTwoPointTimedEventPosition, orderedTwoPointTimedEventEquiv,
      List.Nodup.getEquivOfForallMemList] using hEvent
  have h := idxOf_flatMap_lt_of_event_idxOf_lt twoPointTimedEventAtomicLegs
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
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) := by
  classical
  by_cases hxy : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y
  · let event := orderedTwoPointLegEvent x
    have hx : x ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event] using orderedTwoPointLeg_mem_eventAtomicLegs x
    have hy : y ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedTwoPointLeg_mem_eventAtomicLegs y
    have hσ := idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' σ) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ event) hx hy
    have hυ := idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
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
    exact orderedTwoPointTimedEventPosition_lt_iff_of_eventTime_eq
      τ τ' σ υ (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y) hxTime hyTime

end Fermionic
end SecondQuantization
