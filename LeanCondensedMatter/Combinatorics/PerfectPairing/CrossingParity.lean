import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Order

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

/-- Endpoint inversion counts are unchanged when either pair is independently reversed. -/
theorem pairEndpointInversionCount_eq_of_eq_or_swap {α : Type*} [LT α] [DecidableLT α]
    (left right left' right' : α × α)
    (hl : left = left' ∨ left = left'.swap)
    (hr : right = right' ∨ right = right'.swap) :
    pairEndpointInversionCount left right = pairEndpointInversionCount left' right' := by
  rcases hl with hl | hl <;> rcases hr with hr | hr <;>
    simp only [hl, hr, pairEndpointInversionCount, Prod.swap] <;> ac_rfl

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
  have hac : a < c ↔ ¬ c < a := by
    constructor <;> intro h <;> order
  have had : a < d ↔ ¬ d < a := by
    constructor <;> intro h <;> order
  have hbd : b < d ↔ ¬ d < b := by
    constructor <;> intro h <;> order
  by_cases hca : c < a <;> by_cases hda : d < a <;>
    by_cases hcb : c < b <;> by_cases hdb : d < b
  all_goals
    first
    | exfalso; order
    | simp [pairEndpointInversionCount, Crosses, hac, had, hbd, hca, hda, hcb, hdb]

/-- Distinct normalized pairs have inversion parity equal to their geometric crossing indicator. -/
theorem PairingOn.pairEndpointInversionCount_modEq_crossesIndicator
    {α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (p q : pairing.NormalizedPair) (hne : p ≠ q) :
    Nat.ModEq 2 (pairEndpointInversionCount p.1 q.1)
      (if Crosses p.1 q.1 ∨ Crosses q.1 p.1 then 1 else 0) := by
  have hEnds := pairing.normalizedPair_endpoints_ne_of_ne p q hne
  exact (pairEndpointInversionCount_mod_two_eq_crossesIndicator p.1 q.1
    (pairing.pairs_normalized p.2) (pairing.pairs_normalized q.2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2).trans (by split_ifs <;> decide)

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
  rw [← Fintype.sum_prod_type]
  rw [← Equiv.sum_comp
    ((Equiv.prodProdProdComm A B (Fin 2) (Fin 2)).trans
      (Equiv.prodCongr leftEquiv rightEquiv))
    (fun x : L × R => if rightPos x.2 < leftPos x.1 then (1 : ℕ) else 0)]
  simp only [Fintype.sum_prod_type]
  refine Nat.ModEq.sum (n := 2) fun p _ => ?_
  refine Nat.ModEq.sum (n := 2) fun q _ => ?_
  refine (pairing.pairEndpointInversionCount_modEq_crossesIndicator
    (left p) (right q) (hdisjoint p q)).symm.trans ?_
  change pairEndpointInversionCount (left p).1 (right q).1 % 2 =
    (∑ i : Fin 2, ∑ j : Fin 2,
      if rightPos (rightEquiv (q, j)) < leftPos (leftEquiv (p, i)) then 1 else 0) % 2
  apply congrArg (fun n : ℕ => n % 2)
  rw [pairEndpointInversionCount_eq_of_eq_or_swap _ _
    (leftPos (leftEquiv (p, 0)), leftPos (leftEquiv (p, 1)))
    (rightPos (rightEquiv (q, 0)), rightPos (rightEquiv (q, 1)))
    (hleft p) (hright q)]
  simp only [Fin.sum_univ_two, pairEndpointInversionCount]
  ac_rfl

section GeometricParity

variable {α ι : Type*} [Fintype α] [LinearOrder α] [Fintype ι] [LinearOrder ι]

private noncomputable def crossIndicator (pairing : PairingOn α) (e : ι ≃ pairing.NormalizedPair)
    (k l : ι) : ℕ :=
  if Crosses (e k).1 (e l).1 then 1 else 0

variable [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι]

private theorem crossingCount_eq_sum_Ioi_crossIndicator (pairing : PairingOn α)
    (e : ι ≃ pairing.NormalizedPair) :
    pairing.crossingCount =
      ∑ k : ι, ∑ l ∈ Finset.Ioi k,
        (crossIndicator pairing e k l + crossIndicator pairing e l k) := by
  classical
  have hdiag : ∀ k : ι, crossIndicator pairing e k k = 0 :=
    fun k => ite_eq_right (not_crosses_self _)
  rw [pairing.crossingCount_eq_sum_sum_crosses_of_equiv e]
  calc
    (∑ k : ι, ∑ l : ι, crossIndicator pairing e k l) =
        ∑ k : ι, ∑ l ∈ ({k} : Finset ι)ᶜ, crossIndicator pairing e k l :=
      Finset.sum_congr rfl fun k _ => by
        rw [← Finset.sum_erase_add Finset.univ (crossIndicator pairing e k)
          (Finset.mem_univ k), hdiag k, add_zero, ← Finset.compl_singleton]
    _ = _ :=
      (Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag
        (fun k l => crossIndicator pairing e l k)).symm

/-- The inversion sum over unordered pairs in any ordered presentation has the parity of
the pairing's crossing count, regardless of each pair's endpoint orientation. -/
theorem PairingOn.sum_Ioi_pairEndpointInversionCount_mod_two_eq_crossingCount
    (pairing : PairingOn α) (e : ι ≃ pairing.NormalizedPair) (present : ι → α × α)
    (hpres : ∀ k, present k = (e k).1 ∨ present k = (e k).1.swap) :
    (∑ k : ι, ∑ l ∈ Finset.Ioi k, pairEndpointInversionCount (present k) (present l)) % 2 =
      pairing.crossingCount % 2 := by
  classical
  rw [crossingCount_eq_sum_Ioi_crossIndicator pairing e]
  refine Nat.ModEq.sum (n := 2) fun k _ => ?_
  refine Nat.ModEq.sum (n := 2) fun l hl => ?_
  change pairEndpointInversionCount (present k) (present l) % 2 =
    (crossIndicator pairing e k l + crossIndicator pairing e l k) % 2
  rw [pairEndpointInversionCount_eq_of_eq_or_swap _ _ _ _ (hpres k) (hpres l),
    crossIndicator, crossIndicator, crossesIndicator_add]
  exact pairing.pairEndpointInversionCount_modEq_crossesIndicator (e k) (e l)
    (fun h => (ne_of_lt (Finset.mem_Ioi.1 hl)) (e.injective h))

end GeometricParity

end Combinatorics
