import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing

set_option linter.style.header false

/-!
# Crossing parity from endpoint inversions

For two normalized pairs with disjoint endpoints, geometric crossing is equivalent to odd parity of
the four cross-pair endpoint comparisons. The result depends only on the order of the endpoints,
not on their representation as finite positions.
-/

namespace Combinatorics

/-- Select endpoint `0` or endpoint `1` of an ordered pair. -/
def pairEndpointAt {α : Type*} (pair : α × α) (k : Fin 2) : α :=
  if k = 0 then pair.1 else pair.2

/-- Number of endpoints of `right` that occur before endpoints of `left`. -/
def pairEndpointInversionCount {α : Type*} [LT α] [DecidableLT α]
    (left right : α × α) : ℕ :=
  (if right.1 < left.1 then 1 else 0) +
    (if right.2 < left.1 then 1 else 0) +
    (if right.1 < left.2 then 1 else 0) +
    (if right.2 < left.2 then 1 else 0)

/-- The four endpoint comparisons as a finite double sum. -/
theorem pairEndpointInversionCount_eq_sum {α : Type*} [LT α] [DecidableLT α]
    (left right : α × α) :
    pairEndpointInversionCount left right =
      ∑ i : Fin 2, ∑ j : Fin 2,
        if pairEndpointAt right j < pairEndpointAt left i then 1 else 0 := by
  simp [pairEndpointInversionCount, pairEndpointAt, Fin.sum_univ_two,
    add_comm, add_left_comm]

/-- Indicator-valued form of crossing parity. -/
theorem pairEndpointInversionCount_mod_two_eq_crossesIndicator {α : Type*} [LinearOrder α]
    (left right : α × α)
    (hleft : left.1 < left.2) (hright : right.1 < right.2)
    (h11 : left.1 ≠ right.1) (h12 : left.1 ≠ right.2)
    (h21 : left.2 ≠ right.1) (h22 : left.2 ≠ right.2) :
    pairEndpointInversionCount left right % 2 =
      if Crosses left right ∨ Crosses right left then 1 else 0 := by
  rcases left with ⟨a, b⟩
  rcases right with ⟨c, d⟩
  simp only at hleft hright h11 h12 h21 h22 ⊢
  rcases lt_or_gt_of_ne h11 with hac | hca
  · have hca : ¬ c < a := not_lt_of_gt hac
    have hda : ¬ d < a := not_lt_of_gt (hac.trans hright)
    rcases lt_or_gt_of_ne h21 with hbc | hcb
    · have hcb : ¬ c < b := not_lt_of_gt hbc
      have hdb : ¬ d < b := not_lt_of_gt (hbc.trans hright)
      simp [pairEndpointInversionCount, Crosses, *]
    · rcases lt_or_gt_of_ne h22 with hbd | hdb
      · have hdb : ¬ d < b := not_lt_of_gt hbd
        simp [pairEndpointInversionCount, Crosses, *]
      · have hbd : ¬ b < d := not_lt_of_gt hdb
        simp [pairEndpointInversionCount, Crosses, *]
  · have hac : ¬ a < c := not_lt_of_gt hca
    have hcb : c < b := hca.trans hleft
    rcases lt_or_gt_of_ne h12 with had | hda
    · have hda : ¬ d < a := not_lt_of_gt had
      rcases lt_or_gt_of_ne h22 with hbd | hdb
      · have hdb : ¬ d < b := not_lt_of_gt hbd
        simp [pairEndpointInversionCount, Crosses, *]
      · simp [pairEndpointInversionCount, Crosses, *]
    · have had : ¬ a < d := not_lt_of_gt hda
      have hdb : d < b := hda.trans hleft
      simp [pairEndpointInversionCount, Crosses, *]

end Combinatorics
