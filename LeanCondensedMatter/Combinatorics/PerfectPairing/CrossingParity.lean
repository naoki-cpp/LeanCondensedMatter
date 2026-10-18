import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# Crossing parity from endpoint inversions

For two normalized pairs with disjoint endpoints, geometric crossing is equivalent to odd parity of
the four cross-pair endpoint comparisons.
-/

namespace Combinatorics

/-- Select endpoint `0` or endpoint `1` of an ordered pair. -/
def pairEndpointAt {n : ℕ} (pair : Fin (2 * n) × Fin (2 * n)) (k : Fin 2) : Fin (2 * n) :=
  if k = 0 then pair.1 else pair.2

/-- Number of endpoints of `right` that occur before endpoints of `left`. -/
def pairEndpointInversionCount {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) : ℕ :=
  (if right.1 < left.1 then 1 else 0) +
    (if right.2 < left.1 then 1 else 0) +
    (if right.1 < left.2 then 1 else 0) +
    (if right.2 < left.2 then 1 else 0)

/-- The four endpoint comparisons as a finite double sum. -/
theorem pairEndpointInversionCount_eq_sum {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) :
    pairEndpointInversionCount left right =
      ∑ i : Fin 2, ∑ j : Fin 2,
        if pairEndpointAt right j < pairEndpointAt left i then 1 else 0 := by
  simp [pairEndpointInversionCount, pairEndpointAt, Fin.sum_univ_two,
    add_assoc, add_comm, add_left_comm]

/-- Indicator-valued form of crossing parity. -/
theorem pairEndpointInversionCount_mod_two_eq_crossesIndicator {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n))
    (hleft : left.1 < left.2) (hright : right.1 < right.2)
    (h11 : left.1 ≠ right.1) (h12 : left.1 ≠ right.2)
    (h21 : left.2 ≠ right.1) (h22 : left.2 ≠ right.2) :
    pairEndpointInversionCount left right % 2 =
      if Crosses left right ∨ Crosses right left then 1 else 0 := by
  rcases left with ⟨a, b⟩
  rcases right with ⟨c, d⟩
  simp only at hleft hright h11 h12 h21 h22 ⊢
  simp only [pairEndpointInversionCount, Crosses]
  omega

end Combinatorics
