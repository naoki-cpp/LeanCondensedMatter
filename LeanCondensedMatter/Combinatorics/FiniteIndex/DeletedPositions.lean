import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Ordered positions after deleting two entries

This module supplies the increasing equivalence from a smaller `Fin` type onto the positions left
after deleting `0` and one further nonzero position.  It is pure finite-index combinatorics.
-/

namespace Combinatorics
namespace FiniteIndex

/-- Positions left after deleting `0` and a distinct position `j`. -/
def deletedPositions (n : ℕ) (j : Fin (2 * (n + 1)))
    (_hzero : (0 : Fin (2 * (n + 1))) ≠ j) : Finset (Fin (2 * (n + 1))) :=
  (Finset.univ.erase 0).erase j

@[simp]
theorem card_deletedPositions (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    (deletedPositions n j hzero).card = 2 * n := by
  simp [deletedPositions, Nat.mul_succ, Ne.symm hzero]

/-- Increasing bijection from `Fin (2 * n)` onto the remaining positions. -/
noncomputable def deletedPositionsOrderIso (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    Fin (2 * n) ≃o deletedPositions n j hzero :=
  (deletedPositions n j hzero).orderIsoOfFin (card_deletedPositions n j hzero)

@[simp]
theorem deletedPositionsOrderIso_mem (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) (i : Fin (2 * n)) :
    ((deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1))) ∈
      deletedPositions n j hzero) :=
  (deletedPositionsOrderIso n j hzero i).property

theorem deletedPositionsOrderIso_strictMono (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    StrictMono (fun i : Fin (2 * n) =>
      (deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1)))) := by
  intro i k hik
  exact deletedPositionsOrderIso n j hzero |>.strictMono hik

/-- The order isomorphism is independent of the proof that `j ≠ 0`. -/
theorem deletedPositionsOrderIso_congr (n : ℕ) {j j' : Fin (2 * (n + 1))} (h : j = j')
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j)
    (hzero' : (0 : Fin (2 * (n + 1))) ≠ j') (i : Fin (2 * n)) :
    (deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1))) =
      (deletedPositionsOrderIso n j' hzero' i : Fin (2 * (n + 1))) := by
  subst h
  rfl

end FiniteIndex
end Combinatorics
