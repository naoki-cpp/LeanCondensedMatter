import LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositions

set_option linter.style.header false

/-!
# Deleted positions via `Fin.succAbove`

The canonical increasing equivalence after deleting `0` and `k.succ` agrees with the explicit map
`i ↦ (k.succAbove i).succ`.
-/

namespace Combinatorics
namespace FiniteIndex

/-- Decompose `deletedPositionsOrderIso` into `succAbove` followed by `succ`. -/
theorem deletedPositionsOrderIso_eq_succ_succAbove (n : ℕ) (k : Fin (2 * n + 1))
    (j : Fin (2 * (n + 1))) (hj : j = k.succ)
    (hzero : (0 : Fin (2 * (n + 1))) ≠ j) :
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

end FiniteIndex
end Combinatorics
