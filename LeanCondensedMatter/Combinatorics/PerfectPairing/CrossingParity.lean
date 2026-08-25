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

/-- A Boolean-style inversion indicator is the corresponding power of `-1`. -/
theorem if_negOne_one_eq_negOne_pow_indicator (p : Prop) [Decidable p] :
    (if p then (-1 : ℤˣ) else 1) = (-1) ^ (if p then 1 else 0) := by
  by_cases hp : p <;> simp [hp]

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

/-- `crossingCount` as a `0`-or-`1` sum over all ordered normalized-pair pairs. -/
theorem Pairing.crossingCount_eq_sum_crosses {n : ℕ} (pairing : Pairing n) :
    pairing.crossingCount =
      ∑ x : pairing.NormalizedPair × pairing.NormalizedPair,
        if Crosses x.1.1 x.2.1 then 1 else 0 := by
  classical
  rw [pairing.crossingCount_eq_card_crossingPair]
  have hcard :
      Fintype.card pairing.CrossingPair =
        ((Finset.univ : Finset (pairing.NormalizedPair × pairing.NormalizedPair)).filter
          fun x => Crosses x.1.1 x.2.1).card := by
    exact Fintype.card_of_subtype
      (p := fun x : pairing.NormalizedPair × pairing.NormalizedPair => Crosses x.1.1 x.2.1)
      ((Finset.univ : Finset (pairing.NormalizedPair × pairing.NormalizedPair)).filter
        fun x => Crosses x.1.1 x.2.1)
      (fun x => by simp)
  rw [hcard]
  simp

/-- Double-sum form of `crossingCount_eq_sum_crosses`. -/
theorem Pairing.crossingCount_eq_sum_sum_crosses {n : ℕ} (pairing : Pairing n) :
    pairing.crossingCount =
      ∑ p : pairing.NormalizedPair, ∑ q : pairing.NormalizedPair,
        if Crosses p.1 q.1 then 1 else 0 := by
  rw [pairing.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]

/-- Two normalized pairs with disjoint endpoints cross in one orientation exactly when their four
cross-pair endpoint comparisons have odd parity. -/
theorem pairEndpointInversionCount_mod_two_eq_one_iff_crosses {n : ℕ}
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

/-- Pointwise natural-number congruence lifts to a finite sum. -/
theorem finset_sum_modEq {α : Type*} (n : ℕ) (s : Finset α) (f g : α → ℕ)
    (h : ∀ x ∈ s, Nat.ModEq n (f x) (g x)) :
    Nat.ModEq n (∑ x ∈ s, f x) (∑ x ∈ s, g x) :=
  Nat.ModEq.sum h

/-- Pointwise natural-number congruence lifts to a sum over a finite type. -/
theorem fintype_sum_modEq {α : Type*} [Fintype α] (n : ℕ) (f g : α → ℕ)
    (h : ∀ x, Nat.ModEq n (f x) (g x)) :
    Nat.ModEq n (∑ x, f x) (∑ x, g x) := by
  simpa using finset_sum_modEq n (Finset.univ : Finset α) f g (fun x _ => h x)

/-- Pointwise equality modulo two lifts to a finite sum. -/
theorem finset_sum_mod_two_congr {α : Type*} (s : Finset α) (f g : α → ℕ)
    (h : ∀ x ∈ s, f x % 2 = g x % 2) :
    (∑ x ∈ s, f x) % 2 = (∑ x ∈ s, g x) % 2 := by
  exact finset_sum_modEq 2 s f g h

/-- Pointwise equality modulo two lifts to a sum over a finite type. -/
theorem fintype_sum_mod_two_congr {α : Type*} [Fintype α] (f g : α → ℕ)
    (h : ∀ x, f x % 2 = g x % 2) :
    (∑ x, f x) % 2 = (∑ x, g x) % 2 := by
  exact fintype_sum_modEq 2 f g h

/-- An off-diagonal sum vanishes modulo `n` when each term cancels with its swapped term. -/
theorem finset_sum_offDiag_modEq_zero_of_pair_add_modEq_zero {α : Type*}
    (n : ℕ) (s : Finset α) (f : α → α → ℕ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.ModEq n (f a b + f b a) 0) :
    Nat.ModEq n (∑ p ∈ s.offDiag, f p.1 p.2) 0 := by
  classical
  have hoff : (∑ p ∈ s.offDiag, (f p.1 p.2 : ZMod n)) = 0 := by
    refine Finset.sum_involution
      (s := s.offDiag)
      (f := fun p => (f p.1 p.2 : ZMod n))
      (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_offDiag] at hp
      simpa using
        (ZMod.natCast_eq_natCast_iff (f a b + f b a) 0 n).2
          (hpair a hp.1 b hp.2.1 hp.2.2)
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
  apply (ZMod.natCast_eq_natCast_iff _ 0 n).1
  simpa using hoff

/-- If every symmetric off-diagonal pair is zero modulo `n`, a finite double sum is congruent to its
diagonal modulo `n`. -/
theorem finset_sum_sum_modEq_diag_of_pair_add_modEq_zero {α : Type*}
    (n : ℕ) (s : Finset α) (f : α → α → ℕ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.ModEq n (f a b + f b a) 0) :
    Nat.ModEq n (∑ a ∈ s, ∑ b ∈ s, f a b) (∑ a ∈ s, f a a) := by
  classical
  have hoff :=
    finset_sum_offDiag_modEq_zero_of_pair_add_modEq_zero n s f hpair
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
