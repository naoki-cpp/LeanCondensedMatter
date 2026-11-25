module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Fin.Basic

public section

set_option linter.style.header false

/-!
# Ordered positions after deleting two entries

This module supplies the increasing equivalence from a smaller `Fin` type onto the positions left
after deleting `0` and one further nonzero position. It is pure finite-index combinatorics.
-/

namespace Combinatorics
namespace FiniteIndex

/-- Positions left after deleting `0` and a position `j`. Distinctness is needed only when
proving that the result has cardinality `n`. -/
@[expose] def deletedPositions (n : ℕ) (j : Fin (n + 2)) : Finset (Fin (n + 2)) :=
  (Finset.univ.erase 0).erase j

@[simp]
theorem card_deletedPositions (n : ℕ) (j : Fin (n + 2))
    (hzero : j ≠ (0 : Fin (n + 2))) :
    (deletedPositions n j).card = n := by
  simp [deletedPositions, hzero]

/-- Increasing bijection from `Fin (n)` onto the remaining positions. -/
@[expose] noncomputable def deletedPositionsOrderIso (n : ℕ) (j : Fin (n + 2))
    (hzero : j ≠ (0 : Fin (n + 2))) :
    Fin (n) ≃o deletedPositions n j :=
  (deletedPositions n j).orderIsoOfFin (card_deletedPositions n j hzero)

/-- The increasing enumeration of the remaining positions first skips the deleted nonzero
position in the predecessor coordinates, then skips zero by taking the successor. -/
theorem deletedPositionsOrderIso_apply (n : ℕ) (j : Fin (n + 2)) (hj : j ≠ 0)
    (i : Fin n) :
    (deletedPositionsOrderIso n j hj i : Fin (n + 2)) =
      (((j.pred hj).succAbove i).succ) := by
  let k := j.pred hj
  have hj' : j = k.succ := (Fin.succ_pred _ _).symm
  have hmem : ∀ i : Fin n, ((k.succAbove i).succ : Fin (n + 2)) ∈
      deletedPositions n j := by
    intro i
    simp only [deletedPositions, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨?_, Fin.succ_ne_zero _⟩
    rw [hj']
    exact fun h => Fin.succAbove_ne k i (Fin.succ_injective _ h)
  have hmono : StrictMono (fun i : Fin n => ((k.succAbove i).succ : Fin (n + 2))) :=
    Fin.strictMono_succ.comp (Fin.strictMono_succAbove k)
  have huniq := Finset.orderEmbOfFin_unique (card_deletedPositions n j hj) hmem hmono
  have h1 : (deletedPositionsOrderIso n j hj i : Fin (n + 2)) =
      Finset.orderEmbOfFin (deletedPositions n j) (card_deletedPositions n j hj) i :=
    Finset.coe_orderIsoOfFin_apply _ _ i
  rw [h1, ← huniq]

/-- Separate the two deleted positions (false for zero, true for the other position) from the
increasingly enumerated remaining positions. -/
@[expose] noncomputable def deletedPositionsSumEquiv (n : ℕ) (j : Fin (n + 2)) (hj : j ≠ 0) :
    Bool ⊕ Fin n ≃ Fin (n + 2) where
  toFun := Sum.elim (fun b => if b then j else 0) (fun i => deletedPositionsOrderIso n j hj i)
  invFun x :=
    if h0 : x = 0 then Sum.inl false
    else if hj' : x = j then Sum.inl true
    else Sum.inr ((deletedPositionsOrderIso n j hj).symm
      ⟨x, by simp [deletedPositions, h0, hj']⟩)
  left_inv := by
    rintro (b | i)
    · cases b
      · rfl
      · simp [hj]
    · have hm := Finset.mem_erase.mp (deletedPositionsOrderIso n j hj i).property
      have h0 := (Finset.mem_erase.mp hm.2).1
      simp [h0, hm.1]
  right_inv := by
    intro x
    by_cases h0 : x = 0
    · subst x
      rfl
    · by_cases hxj : x = j
      · subst x
        simp [hj]
      · simp [h0, hxj]

end FiniteIndex
end Combinatorics
