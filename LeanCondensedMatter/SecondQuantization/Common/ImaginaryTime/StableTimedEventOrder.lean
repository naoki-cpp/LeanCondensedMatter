import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Prod.Lex.Basic

set_option linter.style.header false

/-!
# Shared stable order for timed events

This module provides the common order relation used to sort finite event families by decreasing
time, with a natural-number rank breaking ties. It also records how the rank induced by
`finSumFinEquiv` is preserved by strictly monotone reindexings of both summands. Event types and
their rank definitions remain with their domain-specific ordering modules.
-/

namespace SecondQuantization
namespace Common

private def finSumRank {m n : ℕ} (event : Fin m ⊕ Fin n) : ℕ :=
  (finSumFinEquiv event : Fin (m + n)).val

/-- The rank order induced by `finSumFinEquiv` is preserved and reflected by componentwise
strictly monotone reindexings of a finite sum. -/
theorem finSumFinEquiv_map_val_le_iff
    {m₁ m₂ n₁ n₂ : ℕ}
    {f : Fin m₁ → Fin m₂} {g : Fin n₁ → Fin n₂}
    (hf : StrictMono f) (hg : StrictMono g)
    (a b : Fin m₁ ⊕ Fin n₁) :
    ((finSumFinEquiv (Sum.map f g a) : Fin (m₂ + n₂)).val ≤
      (finSumFinEquiv (Sum.map f g b) : Fin (m₂ + n₂)).val) ↔
    ((finSumFinEquiv a : Fin (m₁ + n₁)).val ≤
      (finSumFinEquiv b : Fin (m₁ + n₁)).val) := by
  change finSumRank (Sum.map f g a) ≤ finSumRank (Sum.map f g b) ↔
    finSumRank a ≤ finSumRank b
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          simpa [finSumRank] using hf.le_iff_le
      | inr b =>
          have ha := a.isLt
          have hfa := (f a).isLt
          simp [finSumRank]
          omega
  | inr a =>
      cases b with
      | inl b =>
          have hb := b.isLt
          have hfb := (f b).isLt
          simp [finSumRank]
          omega
      | inr b =>
          have h : g a ≤ g b ↔ a ≤ b := hg.le_iff_le
          simp [finSumRank] at h ⊢
          omega

/-- Lexicographic key for stable event ordering: later times come first, then lower ranks. -/
private def stableTimedEventKey {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    (a : α) : OrderDual ℝ ×ₗ ℕ :=
  toLex (OrderDual.toDual (time a), rank a)

/-- Stable non-strict precedence: later times come first, and rank breaks equal-time ties. -/
def stableTimedEventBeforeOrEqual {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    (a b : α) : Prop :=
  stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b

/-- Explicit logical form of the lexicographic stable event order. -/
theorem stableTimedEventBeforeOrEqual_iff {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    (a b : α) :
    stableTimedEventBeforeOrEqual time rank a b ↔
      time b < time a ∨ (time a = time b ∧ rank a ≤ rank b) := by
  simp [stableTimedEventBeforeOrEqual, stableTimedEventKey, Prod.Lex.toLex_le_toLex]

theorem stableTimedEventBeforeOrEqual_total {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    (a b : α) :
    stableTimedEventBeforeOrEqual time rank a b ∨
      stableTimedEventBeforeOrEqual time rank b a := by
  change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b ∨
    stableTimedEventKey time rank b ≤ stableTimedEventKey time rank a
  exact le_total _ _

theorem stableTimedEventBeforeOrEqual_trans {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    {a b c : α}
    (hab : stableTimedEventBeforeOrEqual time rank a b)
    (hbc : stableTimedEventBeforeOrEqual time rank b c) :
    stableTimedEventBeforeOrEqual time rank a c := by
  change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b at hab
  change stableTimedEventKey time rank b ≤ stableTimedEventKey time rank c at hbc
  change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank c
  exact hab.trans hbc

theorem stableTimedEventBeforeOrEqual_antisymm {α : Type*} (time : α → ℝ)
    (rank : α → ℕ) (rank_injective : Function.Injective rank) {a b : α}
    (hab : stableTimedEventBeforeOrEqual time rank a b)
    (hba : stableTimedEventBeforeOrEqual time rank b a) :
    a = b := by
  change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b at hab
  change stableTimedEventKey time rank b ≤ stableTimedEventKey time rank a at hba
  have hkey : stableTimedEventKey time rank a = stableTimedEventKey time rank b :=
    le_antisymm hab hba
  apply rank_injective
  have hrank :=
    congrArg (fun x : OrderDual ℝ ×ₗ ℕ => (ofLex x).2) hkey
  simpa [stableTimedEventKey] using hrank

/-- Insertion sort by stable timed-event precedence is pairwise ordered. -/
theorem pairwise_insertionSort_stableTimedEventBeforeOrEqual {α : Type*}
    (time : α → ℝ) (rank : α → ℕ) (l : List α) :
    (List.insertionSort (stableTimedEventBeforeOrEqual time rank) l).Pairwise
      (stableTimedEventBeforeOrEqual time rank) := by
  letI : Std.Total (stableTimedEventBeforeOrEqual time rank) :=
    ⟨fun a b => stableTimedEventBeforeOrEqual_total time rank a b⟩
  letI : IsTrans α (stableTimedEventBeforeOrEqual time rank) :=
    ⟨fun a b c hab hbc => stableTimedEventBeforeOrEqual_trans time rank hab hbc⟩
  exact List.pairwise_insertionSort _ _

end Common
end SecondQuantization
