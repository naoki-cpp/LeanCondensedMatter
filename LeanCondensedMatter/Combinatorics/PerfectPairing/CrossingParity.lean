import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import Mathlib.Algebra.BigOperators.ModEq

set_option linter.style.header false

/-!
# Crossing parity from endpoint inversions

For two normalized pairs with disjoint endpoints, geometric crossing is equivalent to odd parity of
the four cross-pair endpoint comparisons. The result depends only on the order of the endpoints,
not on their representation as finite positions.
-/

namespace Combinatorics

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
  simp only [pairEndpointInversionCount, Fin.sum_univ_two, pairEndpointAt_zero,
    pairEndpointAt_one]
  ac_rfl

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

/-- Geometric crossings between disjoint families of normalized pairs have the parity of the
inversions between their endpoint positions. Each local pair may be presented in either endpoint
order: the inversion sum counts all four endpoint comparisons independently of that choice. -/
theorem PairingOn.sum_geometricCrossings_mod_two_eq_positionInversions
    {α A B L R : Type*} [Fintype α] [LinearOrder α]
    [Fintype A] [Fintype B] [Fintype L] [Fintype R]
    (pairing : PairingOn α) (left : A → pairing.NormalizedPair)
    (right : B → pairing.NormalizedPair) (hdisjoint : ∀ p q, left p ≠ right q)
    (leftEquiv : A × Fin 2 ≃ L) (rightEquiv : B × Fin 2 ≃ R)
    (leftPos : L → α) (rightPos : R → α)
    (hleft : ∀ p, (left p).1 =
        (leftPos (leftEquiv (p, 0)), leftPos (leftEquiv (p, 1))) ∨
      (left p).1 = (leftPos (leftEquiv (p, 1)), leftPos (leftEquiv (p, 0))))
    (hright : ∀ q, (right q).1 =
        (rightPos (rightEquiv (q, 0)), rightPos (rightEquiv (q, 1))) ∨
      (right q).1 = (rightPos (rightEquiv (q, 1)), rightPos (rightEquiv (q, 0)))) :
    (∑ x : A × B, if Crosses (left x.1).1 (right x.2).1 ∨
        Crosses (right x.2).1 (left x.1).1 then 1 else 0) % 2 =
      (∑ p : L, ∑ q : R, if rightPos q < leftPos p then 1 else 0) % 2 := by
  classical
  have hparity :
      (∑ x : A × B, if Crosses (left x.1).1 (right x.2).1 ∨
        Crosses (right x.2).1 (left x.1).1 then 1 else 0) % 2 =
      (∑ x : A × B, pairEndpointInversionCount (left x.1).1 (right x.2).1) % 2 := by
    symm
    simpa [Nat.ModEq] using
      (Nat.ModEq.sum
        (n := 2)
        (s := (Finset.univ : Finset (A × B)))
        (f := fun x => pairEndpointInversionCount (left x.1).1 (right x.2).1)
        (g := fun x =>
          if Crosses (left x.1).1 (right x.2).1 ∨
            Crosses (right x.2).1 (left x.1).1 then 1 else 0)
        (fun x _ => by
          have hEnds := pairing.normalizedPair_endpoints_ne_of_ne
            (left x.1) (right x.2) (hdisjoint x.1 x.2)
          exact (pairEndpointInversionCount_mod_two_eq_crossesIndicator
            (left x.1).1 (right x.2).1
            (pairing.pairs_normalized (left x.1).2)
            (pairing.pairs_normalized (right x.2).2)
            hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2).trans
              (by split_ifs <;> decide)))
  have hsum :
      (∑ x : A × B, pairEndpointInversionCount (left x.1).1 (right x.2).1) =
        ∑ x : (A × B) × (Fin 2 × Fin 2),
          if rightPos (rightEquiv (x.1.2, x.2.2)) <
            leftPos (leftEquiv (x.1.1, x.2.1)) then 1 else 0 := by
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rcases hleft p with hp | hp <;> rcases hright q with hq | hq
    all_goals
      simp only [hp, hq, Fin.sum_univ_two, pairEndpointInversionCount]
      ac_rfl
  have hreindex :
      (∑ x : (A × B) × (Fin 2 × Fin 2),
        if rightPos (rightEquiv (x.1.2, x.2.2)) <
          leftPos (leftEquiv (x.1.1, x.2.1)) then 1 else 0) =
        ∑ x : L × R, if rightPos x.2 < leftPos x.1 then 1 else 0 := by
    refine Fintype.sum_equiv
      ((Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodCongr leftEquiv rightEquiv))
      _ _ ?_
    intro x
    rfl
  rw [hparity, hsum, hreindex, Fintype.sum_prod_type]

end Combinatorics
