import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositionsSuccAbove
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn

set_option linter.style.header false

/-!
# `Pairing.eraseZeroOrderIso` via `Fin.succAbove`

This module specializes the general finite-index deletion equivalence to the pairing recursion and
connects it to `List.eraseIdx`.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics.FiniteIndex

/-- The increasing map used by `eraseZeroPair` is `succAbove` followed by `succ`. -/
theorem Pairing.eraseZeroOrderIso_eq_succ_succAbove {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    (pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))) =
      (((pairing.partner 0).pred (pairing.partner_ne 0)).succAbove i).succ := by
  rw [Pairing.eraseZeroOrderIso]
  exact deletedPositionsOrderIso_eq_succ_succAbove n
    ((pairing.partner 0).pred (pairing.partner_ne 0)) (pairing.partner 0)
    (Fin.succ_pred _ _).symm (Ne.symm (pairing.partner_ne 0)) i

/-- Reindexing a family along `eraseZeroOrderIso` equals erasing the partner position from the
tail list. -/
theorem Pairing.ofFn_comp_eraseZeroOrderIso_eq_eraseIdx {α : Type*} {n : ℕ}
    (pairing : Pairing (n + 1)) (C : Fin (2 * (n + 1)) → α) :
    List.ofFn (fun i : Fin (2 * n) => C (pairing.eraseZeroOrderIso i)) =
      (List.ofFn (fun i : Fin (2 * n + 1) => C i.succ)).eraseIdx
        (((pairing.partner 0).pred (pairing.partner_ne 0) : Fin (2 * n + 1)) : ℕ) := by
  rw [List.eraseIdx_ofFn_eq_ofFn_succAbove]
  congr 1
  funext i
  rw [pairing.eraseZeroOrderIso_eq_succ_succAbove]

end BlochDeDominicis
end Common
end SecondQuantization
