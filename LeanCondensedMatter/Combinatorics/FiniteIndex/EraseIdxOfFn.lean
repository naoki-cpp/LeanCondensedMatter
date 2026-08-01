import Mathlib.Data.Fin.SuccPred

set_option linter.style.header false

/-!
# Erasing one `Fin`-indexed entry

`List.ofFn`, erased at position `j`, is `List.ofFn` composed with `Fin.succAbove j`.
-/

namespace Combinatorics
namespace FiniteIndex

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

end FiniteIndex
end Combinatorics
