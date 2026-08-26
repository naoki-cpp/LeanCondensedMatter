import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Ordered positions after deleting two entries

This module supplies the increasing equivalence from a smaller `Fin` type onto the positions left
after deleting `0` and one further nonzero position. It is pure finite-index combinatorics.
-/

namespace Combinatorics
namespace FiniteIndex

/-- Positions left after deleting `0` and a position `j`. Distinctness is needed only when
proving that the result has cardinality `2 * n`. -/
def deletedPositions (n : ℕ) (j : Fin (2 * (n + 1))) : Finset (Fin (2 * (n + 1))) :=
  (Finset.univ.erase 0).erase j

@[simp]
theorem card_deletedPositions (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : j ≠ (0 : Fin (2 * (n + 1)))) :
    (deletedPositions n j).card = 2 * n := by
  simp [deletedPositions, Nat.mul_succ, hzero]

/-- Increasing bijection from `Fin (2 * n)` onto the remaining positions. -/
noncomputable def deletedPositionsOrderIso (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : j ≠ (0 : Fin (2 * (n + 1)))) :
    Fin (2 * n) ≃o deletedPositions n j :=
  (deletedPositions n j).orderIsoOfFin (card_deletedPositions n j hzero)

end FiniteIndex
end Combinatorics
