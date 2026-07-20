import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.Combinatorics.DeletedFinPositionsSuccAbove

set_option linter.style.header false

/-!
# `Pairing.eraseZeroOrderIso`, decomposed into two `Fin.succAbove`/`Fin.succ` steps

The fifth bridging piece toward the general `n`-point Bloch–de Dominicis induction
(`notes/roadmaps/second-quantization.md`'s Phase 9): specializes
`DeletedFinPositionsSuccAbove.lean`'s `deletedPositionsOrderIso_eq_succ_succAbove` to
`Pairing.eraseZeroOrderIso` itself, supplying `k := (pairing.partner 0).pred (pairing.partner_ne
0)` at the one remaining call site the earlier file's docstring deferred — `pairing.partner_ne 0 :
pairing.partner 0 ≠ 0` is exactly the form `Fin.pred` needs, while its `Ne.symm` (`0 ≠
pairing.partner 0`) is the separate form `deletedPositions`'s `hzero` needs; the proof below uses
each at its own call site.
This is what finally lets `Pairing.eraseZeroPair`'s reindexing line up term-by-term against
`EraseIdxOfFn.lean`'s single-`succAbove` description of list erasure.
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

end BlochDeDominicis
end Common
end SecondQuantization
