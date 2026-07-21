import LeanCondensedMatter.Combinatorics.DeletedFinPositions

set_option linter.style.header false

/-!
# `deletedPositionsOrderIso`, decomposed into two `Fin.succAbove`/`Fin.succ` steps

`DeletedFinPositions.lean`'s `deletedPositionsOrderIso` is built directly as a
`Finset.orderIsoOfFin`, not via `Fin.succAbove`, so it cannot be compared term-by-term against
`EraseIdxOfFn.lean`'s single-`succAbove` description of list erasure without further work. This
file closes that gap for the *specific* shape `deletedPositionsOrderIso` always has in this
project — removing `0` together with a *second*, already-nonzero position `j` — by showing it
agrees with the explicit two-step map "avoid `k`'s position among the positions above `0`, then
shift up by one via `Fin.succ` to skip `0` itself", where `k` is `j` written as a successor
(`j = k.succ`, always possible since `j ≠ 0`).

Every use of `deletedPositionsOrderIso n j hzero` in `Combinatorics/PerfectPairing.lean` has `j`
equal to some `pairing.partner 0`, which is always nonzero. Stating the hypothesis as `j = k.succ`
directly, rather than deriving `k := j.pred hj0` inline, keeps this file's own proof free of the
`Fin`-arithmetic casting that `Fin.pred`'s dependent type otherwise forces, deferring that
translation to whichever later step actually invokes this lemma against `Pairing.eraseZeroPair`.
-/

namespace SecondQuantization
namespace Common

/-- **`deletedPositionsOrderIso`, decomposed**: when the removed second position `j` is `k.succ`
for some `k`, the increasing bijection onto `deletedPositions n j hzero` is exactly `i ↦
(k.succAbove i).succ` — first avoid `k`'s position among the `2n+1` positions strictly above `0`,
then shift everything up by one to skip `0` itself. -/
theorem deletedPositionsOrderIso_eq_succ_succAbove (n : ℕ) (k : Fin (2 * n + 1))
    (j : Fin (2 * (n + 1))) (hj : j = k.succ) (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    ∀ i : Fin (2 * n), (deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1))) =
      ((k.succAbove i).succ : Fin (2 * (n + 1))) := by
  have hmem : ∀ i : Fin (2 * n), ((k.succAbove i).succ : Fin (2 * (n + 1))) ∈
      deletedPositions n j hzero := by
    intro i
    simp only [deletedPositions, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨?_, Fin.succ_ne_zero _⟩
    rw [hj]
    exact fun h => Fin.succAbove_ne k i (Fin.succ_injective _ h)
  have hmono : StrictMono (fun i : Fin (2 * n) =>
      ((k.succAbove i).succ : Fin (2 * (n + 1)))) :=
    Fin.strictMono_succ.comp (Fin.strictMono_succAbove k)
  have huniq := Finset.orderEmbOfFin_unique (card_deletedPositions n j hzero) hmem hmono
  intro i
  have h1 : (deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1))) =
      Finset.orderEmbOfFin (deletedPositions n j hzero) (card_deletedPositions n j hzero) i :=
    Finset.coe_orderIsoOfFin_apply _ _ i
  rw [h1, ← huniq]

end Common
end SecondQuantization
