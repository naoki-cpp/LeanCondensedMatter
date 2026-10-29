import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

set_option linter.style.header false

/-!
# Order of blocks in flattened lists

Generic lemmas for comparing `idxOf` positions in a duplicate-free `List.flatMap`. These isolate
list-index bookkeeping from the diagrammatic mixed-event order arguments that use it.
-/

namespace List

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

/-- If one event occurs before another in an event list, every element in the first block
occurs before every element in the second block of the duplicate-free flattened list.
The event list itself need not be duplicate-free (e.g. it may repeat empty blocks). -/
theorem idxOf_flatMap_lt_of_idxOf_lt
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → List β) (events : List α) (a b : α) (x y : β)
    (hFlatNodup : (events.flatMap f).Nodup)
    (ha : a ∈ events) (hb : b ∈ events) (hx : x ∈ f a) (hy : y ∈ f b)
    (hab : events.idxOf a < events.idxOf b) :
    (events.flatMap f).idxOf x < (events.flatMap f).idxOf y := by
  induction events generalizing a b x y with
  | nil => simp at ha
  | cons head tail ih =>
      simp only [List.flatMap_cons] at hFlatNodup ⊢
      have hFlatNodupTail : (tail.flatMap f).Nodup := hFlatNodup.of_append_right
      have hDisjoint : List.Disjoint (f head) (tail.flatMap f) := hFlatNodup.disjoint
      rw [List.mem_cons] at ha hb
      rcases ha with haEq | ha
      · subst a
        rcases hb with hbEq | hb
        · subst b
          exact (Nat.lt_irrefl _ hab).elim
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
          rw [List.idxOf_cons_self] at hab
          omega
        · have hxTail : x ∈ tail.flatMap f := by
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
          have hheadNeA : head ≠ a := by
            intro hEq
            subst a
            exact hxNotHead hx
          have hheadNeB : head ≠ b := by
            intro hEq
            subst b
            exact hyNotHead hy
          have habTail : tail.idxOf a < tail.idxOf b := by
            simpa [List.idxOf_cons_ne tail hheadNeA,
              List.idxOf_cons_ne tail hheadNeB] using hab
          rw [List.idxOf_append_of_notMem hxNotHead,
            List.idxOf_append_of_notMem hyNotHead]
          simpa only [Nat.add_lt_add_iff_left] using
            ih (a := a) (b := b) (x := x) (y := y)
              hFlatNodupTail ha hb hx hy habTail

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
  classical
  obtain ⟨other, hOther, hzOther⟩ := List.mem_flatMap.mp hz
  have heventNe : event ≠ other := by
    intro heq
    subst other
    exact hzOutside hzOther
  have hidxNe : events.idxOf event ≠ events.idxOf other := by
    intro heq
    exact heventNe ((List.idxOf_inj hEvent).mp heq)
  rcases lt_trichotomy (events.idxOf event) (events.idxOf other) with hlt | heq | hgt
  · have hxz : (events.flatMap f).idxOf x < (events.flatMap f).idxOf z :=
      idxOf_flatMap_lt_of_idxOf_lt f events event other x z
        hNodup hEvent hOther hx hzOther hlt
    have hyz : (events.flatMap f).idxOf y < (events.flatMap f).idxOf z :=
      idxOf_flatMap_lt_of_idxOf_lt f events event other y z
        hNodup hEvent hOther hy hzOther hlt
    simp [hxz, hyz]
  · exact (hidxNe heq).elim
  · have hzx : (events.flatMap f).idxOf z < (events.flatMap f).idxOf x :=
      idxOf_flatMap_lt_of_idxOf_lt f events other event z x
        hNodup hOther hEvent hzOther hx hgt
    have hzy : (events.flatMap f).idxOf z < (events.flatMap f).idxOf y :=
      idxOf_flatMap_lt_of_idxOf_lt f events other event z y
        hNodup hOther hEvent hzOther hy hgt
    have hxz : ¬ (events.flatMap f).idxOf x < (events.flatMap f).idxOf z :=
      not_lt_of_ge (le_of_lt hzx)
    have hyz : ¬ (events.flatMap f).idxOf y < (events.flatMap f).idxOf z :=
      not_lt_of_ge (le_of_lt hzy)
    simp [hxz, hyz]

end List
