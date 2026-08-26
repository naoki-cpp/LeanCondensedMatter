import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn

set_option linter.style.header false

/-!
# `Pairing.eraseZeroOrderIso` via `Fin.succAbove`

This module identifies the increasing reindexing used by `eraseZeroPair` with the explicit
`Fin.succAbove` map needed to compare it with `List.eraseIdx`.
-/

namespace Combinatorics

open FiniteIndex

/-- The increasing map used by `eraseZeroPair` is `succAbove` followed by `succ`. -/
theorem Pairing.eraseZeroOrderIso_eq_succ_succAbove {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    (pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))) =
      (((pairing.partner 0).pred (pairing.partner_ne 0)).succAbove i).succ := by
  let k := (pairing.partner 0).pred (pairing.partner_ne 0)
  have hj : pairing.partner 0 = k.succ := (Fin.succ_pred _ _).symm
  rw [Pairing.eraseZeroOrderIso]
  have hmem : ∀ i : Fin (2 * n), ((k.succAbove i).succ : Fin (2 * (n + 1))) ∈
      deletedPositions n (pairing.partner 0) := by
    intro i
    simp only [deletedPositions, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨?_, Fin.succ_ne_zero _⟩
    rw [hj]
    exact fun h => Fin.succAbove_ne k i (Fin.succ_injective _ h)
  have hmono : StrictMono (fun i : Fin (2 * n) =>
      ((k.succAbove i).succ : Fin (2 * (n + 1)))) :=
    Fin.strictMono_succ.comp (Fin.strictMono_succAbove k)
  have huniq := Finset.orderEmbOfFin_unique
    (card_deletedPositions n (pairing.partner 0) (pairing.partner_ne 0)) hmem hmono
  have h1 : (deletedPositionsOrderIso n (pairing.partner 0) (pairing.partner_ne 0) i :
      Fin (2 * (n + 1))) =
      Finset.orderEmbOfFin (deletedPositions n (pairing.partner 0))
        (card_deletedPositions n (pairing.partner 0) (pairing.partner_ne 0)) i :=
    Finset.coe_orderIsoOfFin_apply _ _ i
  rw [h1, ← huniq]

/-- Reindexing a family along `eraseZeroOrderIso` equals erasing the partner position from the
tail list. -/
theorem Pairing.ofFn_comp_eraseZeroOrderIso_eq_eraseIdx {α : Type*} {n : ℕ}
    (pairing : Pairing (n + 1)) (C : Fin (2 * (n + 1)) → α) :
    List.ofFn (fun i : Fin (2 * n) => C (pairing.eraseZeroOrderIso i)) =
      (List.ofFn (fun i : Fin (2 * n + 1) => C i.succ)).eraseIdx
        (((pairing.partner 0).pred (pairing.partner_ne 0) : Fin (2 * n + 1)) : ℕ) := by
  rw [List.eraseIdx_ofFn_eq_ofFn_succAbove]
  congr 1
  funext i
  rw [pairing.eraseZeroOrderIso_eq_succ_succAbove]

end Combinatorics
