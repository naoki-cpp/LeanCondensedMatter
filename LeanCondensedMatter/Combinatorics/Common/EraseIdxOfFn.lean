import Mathlib.Data.Fin.SuccPred

set_option linter.style.header false

/-!
# `List.ofFn`, erased at a position, is `List.ofFn` composed with `Fin.succAbove`

A small general-purpose lemma (no `SecondQuantization`/`AlgebraicFock` dependency at all):
`Fin.succAbove` is the standard description for erasing a *single* position from a `Fin`-indexed
family — `j.succAbove : Fin m → Fin (m + 1)` is the increasing embedding onto `Fin (m + 1) \ {j}`,
so composing a family `C : Fin (m + 1) → α` with it gives `C` restricted to everything but position
`j`. This connects `PeelFirst.lean`'s `List.eraseIdx`-based erasure (`PeelTermsIndexed.lean`'s
`peelTerms_eq_ofFn`) to `Fin`-indexed erasure — the description
`Combinatorics/PerfectPairing.lean`'s `Pairing.eraseZeroPair` needs to line up against (see
`Combinatorics/Common/DeletedFinPositionsSuccAbove.lean` and
`Combinatorics/PerfectPairing/EraseZeroSuccAbove.lean` for the two-position case that lemma
actually uses). This file has no Mathlib precedent (`eraseIdx`/`ofFn`/`succAbove` are never
connected directly), so it is proved from scratch by induction on the family length.
-/

theorem List.eraseIdx_ofFn_eq_ofFn_succAbove {α : Type*} :
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
            List.eraseIdx_ofFn_eq_ofFn_succAbove (fun i : Fin (m + 1) => C i.succ) k,
            List.ofFn_succ]
          congr 1
          congr 1
          funext i
          rw [Fin.succ_succAbove_succ]

