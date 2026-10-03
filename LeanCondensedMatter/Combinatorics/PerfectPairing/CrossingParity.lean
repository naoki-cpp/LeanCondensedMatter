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

/-- Two normalized pairs with disjoint endpoints cross in one orientation exactly when their four
cross-pair endpoint comparisons have odd parity. -/
private theorem pairEndpointInversionCount_mod_two_eq_one_iff_crosses {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n))
    (hleft : left.1 < left.2) (hright : right.1 < right.2)
    (h11 : left.1 ≠ right.1) (h12 : left.1 ≠ right.2)
    (h21 : left.2 ≠ right.1) (h22 : left.2 ≠ right.2) :
    pairEndpointInversionCount left right % 2 = 1 ↔
      Crosses left right ∨ Crosses right left := by
  rcases left with ⟨a, b⟩
  rcases right with ⟨c, d⟩
  simp only at hleft hright h11 h12 h21 h22 ⊢
  by_cases hca : c < a <;>
  by_cases hda : d < a <;>
  by_cases hcb : c < b <;>
  by_cases hdb : d < b <;>
  simp [pairEndpointInversionCount, Crosses, hca, hda, hcb, hdb] <;>
  omega

/-- Indicator-valued form of crossing parity. -/
theorem pairEndpointInversionCount_mod_two_eq_crossesIndicator {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n))
    (hleft : left.1 < left.2) (hright : right.1 < right.2)
    (h11 : left.1 ≠ right.1) (h12 : left.1 ≠ right.2)
    (h21 : left.2 ≠ right.1) (h22 : left.2 ≠ right.2) :
    pairEndpointInversionCount left right % 2 =
      if Crosses left right ∨ Crosses right left then 1 else 0 := by
  by_cases hcross : Crosses left right ∨ Crosses right left
  · simp [hcross,
      (pairEndpointInversionCount_mod_two_eq_one_iff_crosses
        left right hleft hright h11 h12 h21 h22).2 hcross]
  · have hne : pairEndpointInversionCount left right % 2 ≠ 1 := by
      intro h
      exact hcross ((pairEndpointInversionCount_mod_two_eq_one_iff_crosses
        left right hleft hright h11 h12 h21 h22).1 h)
    have hlt : pairEndpointInversionCount left right % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    simp [hcross]
    omega

/-- Two off-diagonal sums are congruent modulo `n` when each unordered pair has the same
combined contribution modulo `n`. -/
theorem finset_sum_offDiag_modEq_of_pair_add_modEq {α : Type*}
    (n : ℕ) (s : Finset α) (f g : α → α → ℕ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      Nat.ModEq n (f a b + f b a) (g a b + g b a)) :
    Nat.ModEq n
      (∑ p ∈ s.offDiag, f p.1 p.2)
      (∑ p ∈ s.offDiag, g p.1 p.2) := by
  classical
  have hzero :
      (∑ p ∈ s.offDiag,
        ((f p.1 p.2 : ZMod n) - (g p.1 p.2 : ZMod n))) = 0 := by
    refine Finset.sum_involution
      (s := s.offDiag)
      (f := fun p =>
        ((f p.1 p.2 : ZMod n) - (g p.1 p.2 : ZMod n)))
      (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_offDiag] at hp
      have hz :
          ((f a b + f b a : ℕ) : ZMod n) =
            ((g a b + g b a : ℕ) : ZMod n) :=
        (ZMod.natCast_eq_natCast_iff _ _ n).2
          (hpair a hp.1 b hp.2.1 hp.2.2)
      simp only [Prod.swap_prod_mk]
      calc
        (f a b : ZMod n) - (g a b : ZMod n) +
            ((f b a : ZMod n) - (g b a : ZMod n)) =
          ((f a b + f b a : ℕ) : ZMod n) -
            ((g a b + g b a : ℕ) : ZMod n) := by
              simp only [Nat.cast_add]
              ring
        _ = 0 := by rw [hz]; simp
    · rintro ⟨a, b⟩ hp _
      simp only [Finset.mem_offDiag] at hp
      intro hswap
      apply hp.2.2
      exact (congrArg Prod.fst hswap).symm
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, hp.2.2.symm⟩
    · rintro ⟨a, b⟩ hp
      rfl
  apply (ZMod.natCast_eq_natCast_iff _ _ n).1
  have hsum :
      (∑ p ∈ s.offDiag, (f p.1 p.2 : ZMod n)) =
        ∑ p ∈ s.offDiag, (g p.1 p.2 : ZMod n) := by
    rw [Finset.sum_sub_distrib] at hzero
    exact sub_eq_zero.mp hzero
  simpa using hsum

/-- An ordering selects one representative from each unordered pair in an off-diagonal sum.

If the combined contribution of each pair agrees modulo `n` with `g a b`, then the sum of `f` over
all ordered distinct pairs agrees with the sum of `g` in the orientation selected by an injective
order. -/
theorem finset_sum_offDiag_modEq_of_pair_add_modEq_of_order {α β : Type*}
    [LinearOrder β] (n : ℕ) (s : Finset α) (order : α → β) (horder : Set.InjOn order s)
    (f g : α → α → ℕ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.ModEq n (f a b + f b a) (g a b)) :
    Nat.ModEq n
      (∑ p ∈ s.offDiag, f p.1 p.2)
      (∑ p ∈ s.offDiag, if order p.1 < order p.2 then g p.1 p.2 else 0) := by
  classical
  apply finset_sum_offDiag_modEq_of_pair_add_modEq n s f
    (fun a b => if order a < order b then g a b else 0)
  intro a ha b hb hab
  by_cases hlt : order a < order b
  · have hnlt : ¬ order b < order a := asymm hlt
    simpa [hlt, hnlt] using hpair a ha b hb hab
  · have hne : order a ≠ order b := fun h => hab (horder ha hb h)
    have hrev : order b < order a := by
      rcases lt_trichotomy (order a) (order b) with h | h | h
      · exact absurd h hlt
      · exact absurd h hne
      · exact h
    simpa [hlt, hrev, add_comm] using hpair b hb a ha hab.symm

/-- If every symmetric off-diagonal pair is zero modulo `n`, a finite double sum is congruent to its
diagonal modulo `n`. -/
private theorem finset_sum_sum_modEq_diag_of_pair_add_modEq_zero {α : Type*}
    (n : ℕ) (s : Finset α) (f : α → α → ℕ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.ModEq n (f a b + f b a) 0) :
    Nat.ModEq n (∑ a ∈ s, ∑ b ∈ s, f a b) (∑ a ∈ s, f a a) := by
  classical
  have hoff :
      Nat.ModEq n (∑ p ∈ s.offDiag, f p.1 p.2) 0 := by
    simpa using
      finset_sum_offDiag_modEq_of_pair_add_modEq n s f (fun _ _ => 0)
        (fun a ha b hb hab => by simpa using hpair a ha b hb hab)
  have hsplit :
      (∑ a ∈ s, ∑ b ∈ s, f a b) =
        (∑ p ∈ s.diag, f p.1 p.2) + ∑ p ∈ s.offDiag, f p.1 p.2 := by
    rw [← Finset.sum_product' s s f]
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag s)]
    rw [Finset.diag_union_offDiag]
  have hdiag :
      (∑ p ∈ s.diag, f p.1 p.2) = ∑ a ∈ s, f a a := by
    simp [Finset.diag]
  rw [hsplit, hdiag]
  simpa using
    (Nat.ModEq.refl (n := n) (∑ a ∈ s, f a a)).add hoff

/-- Finite-type form of `finset_sum_sum_modEq_diag_of_pair_add_modEq_zero`. -/
theorem fintype_sum_sum_modEq_diag_of_pair_add_modEq_zero {α : Type*}
    [Fintype α] (n : ℕ) (f : α → α → ℕ)
    (hpair : ∀ a b, a ≠ b → Nat.ModEq n (f a b + f b a) 0) :
    Nat.ModEq n (∑ a, ∑ b, f a b) (∑ a, f a a) := by
  simpa using finset_sum_sum_modEq_diag_of_pair_add_modEq_zero
    n (Finset.univ : Finset α) f (fun a _ b _ hab => hpair a b hab)

end Combinatorics
