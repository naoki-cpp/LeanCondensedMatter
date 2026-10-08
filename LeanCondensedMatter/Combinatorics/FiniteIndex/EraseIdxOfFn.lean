import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# Erasing one `Fin`-indexed entry

`List.ofFn`, erased at position `j`, is `List.ofFn` composed with `Fin.succAbove j`.  The theorem is
placed in the `List` namespace while its implementation file belongs to finite-index combinatorics.
Sums depending on the selected entry and the remaining list can be reindexed through the same law.
-/

namespace List

/-- Erasing an entry from `List.ofFn C` restricts `C` along `Fin.succAbove`. -/
theorem eraseIdx_ofFn_eq_ofFn_succAbove {α : Type*} :
    {m : ℕ} → (C : Fin (m + 1) → α) → (j : Fin (m + 1)) →
      (List.ofFn C).eraseIdx (j : ℕ) = List.ofFn (fun i : Fin m => C (j.succAbove i))
  | 0, C, j => by
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp
  | m + 1, C, j => by
      induction j using Fin.cases with
      | zero => simp [List.ofFn_succ]
      | succ k =>
          rw [List.ofFn_succ, Fin.val_succ, List.eraseIdx_cons_succ,
            eraseIdx_ofFn_eq_ofFn_succAbove (fun i : Fin (m + 1) => C i.succ) k,
            List.ofFn_succ]
          congr 1
          congr 1
          funext i
          rw [Fin.succ_succAbove_succ]

/-- Reindex a sum over entries and their deleted lists from `List.ofFn` to its original finite
coordinates. -/
theorem sum_getElem_eraseIdx_ofFn {α M : Type*} [AddCommMonoid M] {n : ℕ}
    (C : Fin (n + 1) → α) (f : ℕ → α → List α → M) :
    (∑ i : Fin (List.ofFn C).length,
      f (i : ℕ) ((List.ofFn C)[(i : ℕ)]'i.isLt) ((List.ofFn C).eraseIdx (i : ℕ))) =
      ∑ j : Fin (n + 1), f (j : ℕ) (C j) (List.ofFn fun i : Fin n => C (j.succAbove i)) := by
  have hlen : (List.ofFn C).length = n + 1 := by simp
  rw [← Equiv.sum_comp (finCongr hlen.symm)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [finCongr_apply, Fin.val_cast, List.getElem_ofFn]
  rw [eraseIdx_ofFn_eq_ofFn_succAbove]

end List
