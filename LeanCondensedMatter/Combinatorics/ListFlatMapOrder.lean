import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Order of blocks in flattened lists

Generic lemmas for comparing `idxOf` positions in a duplicate-free `List.flatMap`. These isolate
list-index bookkeeping from the diagrammatic mixed-event order arguments that use it.
-/

namespace List

/-- In a duplicate-free flattened list, two elements of one block have the same order relation to an
element outside that block. -/
theorem idxOf_flatMap_block_lt_uniform
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
theorem idxOf_flatMap_block_lt_iff
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

/-- If one event occurs before another in a duplicate-free event list, every element in the first
block occurs before every element in the second block of the duplicate-free flattened list. -/
theorem idxOf_flatMap_lt_of_idxOf_lt
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → List β) (events : List α) (a b : α) (x y : β)
    (hEventsNodup : events.Nodup) (hFlatNodup : (events.flatMap f).Nodup)
    (ha : a ∈ events) (hb : b ∈ events) (hx : x ∈ f a) (hy : y ∈ f b)
    (hab : events.idxOf a < events.idxOf b) :
    (events.flatMap f).idxOf x < (events.flatMap f).idxOf y := by
  induction events generalizing a b x y with
  | nil => simp at ha
  | cons head tail ih =>
      have hheadNotMem : head ∉ tail := (List.nodup_cons.1 hEventsNodup).1
      have hEventsNodupTail : tail.Nodup := (List.nodup_cons.1 hEventsNodup).2
      simp only [List.flatMap_cons] at hFlatNodup ⊢
      have hFlatNodupTail : (tail.flatMap f).Nodup := hFlatNodup.of_append_right
      have hDisjoint : List.Disjoint (f head) (tail.flatMap f) := hFlatNodup.disjoint
      rw [List.mem_cons] at ha hb
      rcases ha with haEq | ha
      · subst a
        rcases hb with hbEq | hb
        · subst b
          exact (lt_irrefl _ hab).elim
        · have hyTail : y ∈ tail.flatMap f := by
            rw [List.mem_flatMap]
            exact ⟨b, hb, hy⟩
          have hyNotHead : y ∉ f head := by
            intro hyHead
            exact (List.disjoint_left.1 hDisjoint) hyHead hyTail
          rw [List.idxOf_append_of_mem hx,
            List.idxOf_append_of_notMem hyNotHead]
          have hxLt : (f head).idxOf x < (f head).length :=
            List.idxOf_lt_length_of_mem hx
          omega
      · rcases hb with hbEq | hb
        · subst b
          have hheadNeA : head ≠ a := by
            intro hEq
            subst a
            exact hheadNotMem ha
          rw [List.idxOf_cons_ne tail hheadNeA, List.idxOf_cons_self] at hab
          omega
        · have hheadNeA : head ≠ a := by
            intro hEq
            subst a
            exact hheadNotMem ha
          have hheadNeB : head ≠ b := by
            intro hEq
            subst b
            exact hheadNotMem hb
          have habTail : tail.idxOf a < tail.idxOf b := by
            simpa [List.idxOf_cons_ne tail hheadNeA,
              List.idxOf_cons_ne tail hheadNeB] using hab
          have hxTail : x ∈ tail.flatMap f := by
            rw [List.mem_flatMap]
            exact ⟨a, ha, hx⟩
          have hyTail : y ∈ tail.flatMap f := by
            rw [List.mem_flatMap]
            exact ⟨b, hb, hy⟩
          have hxNotHead : x ∉ f head := by
            intro hxHead
            exact (List.disjoint_left.1 hDisjoint) hxHead hxTail
          have hyNotHead : y ∉ f head := by
            intro hyHead
            exact (List.disjoint_left.1 hDisjoint) hyHead hyTail
          rw [List.idxOf_append_of_notMem hxNotHead,
            List.idxOf_append_of_notMem hyNotHead]
          simpa only [Nat.add_lt_add_iff_left] using
            ih (a := a) (b := b) (x := x) (y := y)
              hEventsNodupTail hFlatNodupTail ha hb hx hy habTail

end List
