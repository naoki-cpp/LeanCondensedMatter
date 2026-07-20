import Mathlib.Data.Fin.SuccPred

set_option linter.style.header false

/-!
# `List.ofFn`, erased at a position, is `List.ofFn` composed with `Fin.succAbove`

A small general-purpose lemma (no `SecondQuantization`/`AlgebraicFock` dependency at all) needed
by the third bridging piece toward the general `n`-point Bloch–de Dominicis induction
(`notes/roadmaps/second-quantization.md`'s Phase 9): connecting `PeelFirst.lean`'s
`List.eraseIdx`-based erasure (`PeelTermsIndexed.lean`'s `peelTerms_eq_ofFn`) to
`Combinatorics/PerfectPairing.lean`'s `Fin`-indexed one (`Pairing.eraseZeroPair`, built via
`Combinatorics/DeletedFinPositions.lean`'s `deletedPositionsOrderIso`) needs a common description
of "erase one position from a `Fin`-indexed family" on both sides. `Fin.succAbove` (already used
throughout `Combinatorics/PerfectPairing.lean`'s Mathlib dependencies) is exactly that: `j.succAbove
: Fin m → Fin (m + 1)` is the increasing embedding onto `Fin (m + 1) \ {j}`, so composing a family
`C : Fin (m + 1) → α` with it gives `C` restricted to everything but position `j`. This file has no
Mathlib precedent (`eraseIdx`/`ofFn`/`succAbove` are never connected directly), so it is proved from
scratch by induction on the family length.
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

