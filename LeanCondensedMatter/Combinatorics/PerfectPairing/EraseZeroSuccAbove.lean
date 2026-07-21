import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.Combinatorics.Common.DeletedFinPositionsSuccAbove
import LeanCondensedMatter.Combinatorics.Common.EraseIdxOfFn

set_option linter.style.header false

/-!
# `Pairing.eraseZeroOrderIso`, decomposed into two `Fin.succAbove`/`Fin.succ` steps

Specializes `DeletedFinPositionsSuccAbove.lean`'s `deletedPositionsOrderIso_eq_succ_succAbove` to
`Pairing.eraseZeroOrderIso` itself, supplying `k := (pairing.partner 0).pred (pairing.partner_ne
0)` — `pairing.partner_ne 0 : pairing.partner 0 ≠ 0` is exactly the form `Fin.pred` needs, while
its `Ne.symm` (`0 ≠ pairing.partner 0`) is the separate form `deletedPositions`'s `hzero` needs;
the proof below uses each at its own call site. This lets `Pairing.eraseZeroPair`'s reindexing
line up term-by-term against `EraseIdxOfFn.lean`'s single-`succAbove` description of list erasure
(`ofFn_comp_eraseZeroOrderIso_eq_eraseIdx` below composes the two into a single identity).
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- **`Pairing.eraseZeroOrderIso`, decomposed**: the increasing bijection from `Fin (2 * n)` onto
the positions left after removing `0` and its partner agrees with the explicit two-step map "avoid
`(pairing.partner 0).pred`'s position, then shift up by one via `Fin.succ` to skip `0` itself". -/
theorem Pairing.eraseZeroOrderIso_eq_succ_succAbove {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    (pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))) =
      (((pairing.partner 0).pred (pairing.partner_ne 0)).succAbove i).succ := by
  rw [Pairing.eraseZeroOrderIso]
  exact Common.deletedPositionsOrderIso_eq_succ_succAbove n
    ((pairing.partner 0).pred (pairing.partner_ne 0)) (pairing.partner 0)
    (Fin.succ_pred _ _).symm (Ne.symm (pairing.partner_ne 0)) i

/-- **An operator family reindexed along `eraseZeroOrderIso` is the tail family with one position
erased**: combines `eraseZeroOrderIso_eq_succ_succAbove` with `EraseIdxOfFn.lean`'s
`List.eraseIdx_ofFn_eq_ofFn_succAbove`, giving the single composed identity the general `n`-point
induction actually needs — the family `C` restricted to `pairing.eraseZeroPair`'s surviving
positions is literally `PeelTermsIndexed.lean`'s `peelTerms_eq_ofFn`/`PeelFirst.lean`'s erasure of
the tail list at position `(pairing.partner 0).pred`. -/
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
