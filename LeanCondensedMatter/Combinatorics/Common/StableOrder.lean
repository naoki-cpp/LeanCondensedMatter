import Mathlib.Order.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Sort
import Mathlib.Order.Prod.Lex.Basic

set_option linter.style.header false

/-!
# Stable order with ranked ties

Pullback of the lexicographic order on a reversed primary order and an ordinary
secondary order, together with order preservation for finite-sum ranks.
-/

namespace Combinatorics

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
private def stableTimedEventKey {α T K : Type*} (time : α → T) (rank : α → K)
    (a : α) : OrderDual T ×ₗ K :=
  toLex (OrderDual.toDual (time a), rank a)

/-- Stable non-strict precedence: later times come first, and rank breaks equal-time ties. -/
def stableTimedEventBeforeOrEqual {α T K : Type*} [LinearOrder T] [LinearOrder K] (time : α → T) (rank : α → K)
    (a b : α) : Prop :=
  stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b

/-- Explicit logical form of the lexicographic stable event order. -/
theorem stableTimedEventBeforeOrEqual_iff {α T K : Type*} [LinearOrder T] [LinearOrder K] (time : α → T) (rank : α → K)
    (a b : α) :
    stableTimedEventBeforeOrEqual time rank a b ↔
      time b < time a ∨ (time a = time b ∧ rank a ≤ rank b) := by
  simp [stableTimedEventBeforeOrEqual, stableTimedEventKey, Prod.Lex.toLex_le_toLex]

/-- Preserving every strict time comparison preserves the stable event order,
including equal-time ties resolved by the fixed rank. -/
theorem stableTimedEventBeforeOrEqual_congr {α T K : Type*} [LinearOrder T] [LinearOrder K]
    (t u : α → T) (rank : α → K)
    (h : ∀ a b, t a < t b ↔ u a < u b) (a b : α) :
    stableTimedEventBeforeOrEqual t rank a b ↔
      stableTimedEventBeforeOrEqual u rank a b := by
  have heq : (t a = t b) ↔ (u a = u b) :=
    eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt (h a b) (h b a)
  simp only [stableTimedEventBeforeOrEqual_iff]
  rw [h b a, heq]

instance {α T K : Type*} [LinearOrder T] [LinearOrder K] (time : α → T) (rank : α → K) :
    Std.Total (stableTimedEventBeforeOrEqual time rank) :=
  ⟨fun a b => by
    change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b ∨
      stableTimedEventKey time rank b ≤ stableTimedEventKey time rank a
    exact le_total _ _⟩

instance {α T K : Type*} [LinearOrder T] [LinearOrder K] (time : α → T) (rank : α → K) :
    IsTrans α (stableTimedEventBeforeOrEqual time rank) :=
  ⟨fun a b c hab hbc => by
    change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b at hab
    change stableTimedEventKey time rank b ≤ stableTimedEventKey time rank c at hbc
    change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank c
    exact hab.trans hbc⟩

theorem stableTimedEventBeforeOrEqual_antisymm {α T K : Type*} [LinearOrder T] [LinearOrder K] (time : α → T)
    (rank : α → K) (rank_injective : Function.Injective rank) {a b : α}
    (hab : stableTimedEventBeforeOrEqual time rank a b)
    (hba : stableTimedEventBeforeOrEqual time rank b a) :
    a = b := by
  change stableTimedEventKey time rank a ≤ stableTimedEventKey time rank b at hab
  change stableTimedEventKey time rank b ≤ stableTimedEventKey time rank a at hba
  have hkey : stableTimedEventKey time rank a = stableTimedEventKey time rank b :=
    le_antisymm hab hba
  apply rank_injective
  have hrank :=
    congrArg (fun x : OrderDual T ×ₗ K => (ofLex x).2) hkey
  simpa [stableTimedEventKey] using hrank

end Combinatorics
