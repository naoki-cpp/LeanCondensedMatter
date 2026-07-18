import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Ordered positions after deleting two entries

The finite-temperature Bloch--de Dominicis induction removes position `0` and its partner from
`Fin (2 * (n + 1))`.  The remaining positions are not definitionally a `Fin (2 * n)`, so the
induction needs an explicit order isomorphism before a smaller pairing can be constructed.

This module owns only that reindexing seam.  It does not import the pairing implementation: the
same ordered-finite-set interface can be reused by any later construction that removes two
positions.
-/

namespace SecondQuantization
namespace Common

/-- The positions left after deleting `0` and a distinct position `j`. -/
def deletedPositions (n : ℕ) (j : Fin (2 * (n + 1)))
    (_hzero : (0 : Fin (2 * (n + 1))) ≠ j) : Finset (Fin (2 * (n + 1))) :=
  (Finset.univ.erase 0).erase j

@[simp]
theorem card_deletedPositions (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    (deletedPositions n j hzero).card = 2 * n := by
  simp [deletedPositions, Nat.mul_succ, Ne.symm hzero]

/-- The increasing bijection from `Fin (2 * n)` onto the remaining positions. -/
noncomputable def deletedPositionsOrderIso (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    Fin (2 * n) ≃o deletedPositions n j hzero :=
  (deletedPositions n j hzero).orderIsoOfFin (card_deletedPositions n j hzero)

@[simp]
theorem deletedPositionsOrderIso_mem (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) (i : Fin (2 * n)) :
    ((deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1))) ∈ deletedPositions n j hzero) :=
  (deletedPositionsOrderIso n j hzero i).property

theorem deletedPositionsOrderIso_strictMono (n : ℕ) (j : Fin (2 * (n + 1)))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
    StrictMono (fun i : Fin (2 * n) =>
      (deletedPositionsOrderIso n j hzero i : Fin (2 * (n + 1)))) := by
  intro i k hik
  exact deletedPositionsOrderIso n j hzero |>.strictMono hik

end Common
end SecondQuantization
