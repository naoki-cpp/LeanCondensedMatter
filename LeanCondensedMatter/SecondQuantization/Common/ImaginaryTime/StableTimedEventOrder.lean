import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Shared stable order for timed events

This module provides the common order relation used to sort finite event families by decreasing
time, with a natural-number rank breaking ties. Event types and their rank definitions remain with
their domain-specific ordering modules.
-/

namespace SecondQuantization
namespace Common

/-- Stable non-strict precedence: later times come first, and rank breaks equal-time ties. -/
def stableTimedEventBeforeOrEqual {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    (a b : α) : Prop :=
  time b < time a ∨ (time a = time b ∧ rank a ≤ rank b)

theorem stableTimedEventBeforeOrEqual_total {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    (a b : α) :
    stableTimedEventBeforeOrEqual time rank a b ∨
      stableTimedEventBeforeOrEqual time rank b a := by
  rcases lt_trichotomy (time a) (time b) with hab | hab | hab
  · right
    exact Or.inl hab
  · rcases le_total (rank a) (rank b) with hr | hr
    · left
      exact Or.inr ⟨hab, hr⟩
    · right
      exact Or.inr ⟨hab.symm, hr⟩
  · left
    exact Or.inl hab

theorem stableTimedEventBeforeOrEqual_trans {α : Type*} (time : α → ℝ) (rank : α → ℕ)
    {a b c : α}
    (hab : stableTimedEventBeforeOrEqual time rank a b)
    (hbc : stableTimedEventBeforeOrEqual time rank b c) :
    stableTimedEventBeforeOrEqual time rank a c := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hbc with hbc | ⟨hbcTime, _⟩
    · exact Or.inl (lt_trans hbc hab)
    · exact Or.inl (hbcTime ▸ hab)
  · rcases hbc with hbc | ⟨hbcTime, hbcRank⟩
    · exact Or.inl (habTime ▸ hbc)
    · exact Or.inr ⟨habTime.trans hbcTime, habRank.trans hbcRank⟩

theorem stableTimedEventBeforeOrEqual_antisymm {α : Type*} (time : α → ℝ)
    (rank : α → ℕ) (rank_injective : Function.Injective rank) {a b : α}
    (hab : stableTimedEventBeforeOrEqual time rank a b)
    (hba : stableTimedEventBeforeOrEqual time rank b a) :
    a = b := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hba with hba | ⟨hbaTime, _⟩
    · exact (lt_asymm hab hba).elim
    · rw [hbaTime] at hab
      exact (lt_irrefl _ hab).elim
  · rcases hba with hba | ⟨_, hbaRank⟩
    · rw [habTime] at hba
      exact (lt_irrefl _ hba).elim
    · exact rank_injective (Nat.le_antisymm habRank hbaRank)

end Common
end SecondQuantization
