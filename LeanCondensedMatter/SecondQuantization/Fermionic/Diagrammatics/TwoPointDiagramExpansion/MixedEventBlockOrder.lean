import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Ordering inside mixed-time atomic event blocks

The mixed atomic list is a `flatMap` of event-local atomic-leg lists.  Thus all legs contributed by
one external or interaction event form one contiguous block.  This module records the corresponding
order fact: two positions in the same event block have identical comparison with any position outside
that block.
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

end Fermionic
end SecondQuantization
