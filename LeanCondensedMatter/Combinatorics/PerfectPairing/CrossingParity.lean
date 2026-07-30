import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

set_option linter.style.header false

/-!
# Crossing parity from endpoint inversions

For two normalized pairs with disjoint endpoints, geometric crossing is equivalent to odd parity of
the four cross-pair endpoint comparisons. This is the local combinatorial fact used to turn
cross-component crossing parity into the parity of a block-shuffle inversion count.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- Select endpoint `0` or endpoint `1` of an ordered pair. -/
def pairEndpointAt {n : ℕ} (pair : Fin (2 * n) × Fin (2 * n)) (k : Fin 2) : Fin (2 * n) :=
  if k = 0 then pair.1 else pair.2

/-- Number of endpoints of `right` that occur before endpoints of `left`, counted across all four
cross-pair endpoint comparisons. -/
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

/-- Compatibility equivalence for callers that used the explicitly normalized representation. -/
def Pairing.crossingPairEquivNormalized {n : ℕ} (pairing : Pairing n) :
    pairing.CrossingPair ≃
      {x : pairing.NormalizedPair × pairing.NormalizedPair // Crosses x.1.1 x.2.1} :=
  Equiv.refl _

/-- `crossingCount` as a `0`-or-`1` sum over all ordered normalized-pair pairs. -/
theorem Pairing.crossingCount_eq_sum_crosses {n : ℕ} (pairing : Pairing n) :
    pairing.crossingCount =
      ∑ x : pairing.NormalizedPair × pairing.NormalizedPair,
        if Crosses x.1.1 x.2.1 then 1 else 0 := by
  classical
  rw [pairing.crossingCount_eq_card_crossingPair,
    Fintype.card_congr pairing.crossingPairEquivNormalized]
  have hcard :
      Fintype.card
          {x : pairing.NormalizedPair × pairing.NormalizedPair // Crosses x.1.1 x.2.1} =
        ((Finset.univ : Finset (pairing.NormalizedPair × pairing.NormalizedPair)).filter
          fun x => Crosses x.1.1 x.2.1).card := by
    exact Fintype.card_of_subtype
      (p := fun x : pairing.NormalizedPair × pairing.NormalizedPair => Crosses x.1.1 x.2.1)
      ((Finset.univ : Finset (pairing.NormalizedPair × pairing.NormalizedPair)).filter
        fun x => Crosses x.1.1 x.2.1)
      (fun x => by simp)
  rw [hcard]
  simpa using
    (Finset.sum_boole
      (fun x : pairing.NormalizedPair × pairing.NormalizedPair => Crosses x.1.1 x.2.1)
      Finset.univ).symm

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

/-- Pointwise equality modulo two lifts to a finite sum. -/
theorem finset_sum_mod_two_congr {α : Type*} (s : Finset α) (f g : α → ℕ)
    (h : ∀ x ∈ s, f x % 2 = g x % 2) :
    (∑ x ∈ s, f x) % 2 = (∑ x ∈ s, g x) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.mem_insert] at h
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mod, Nat.add_mod,
        h a (Or.inl rfl), ih (fun x hx => h x (Or.inr hx))]
      simpa only [Nat.mod_mod] using
        (Nat.add_mod (g a) (∑ x ∈ s, g x) 2).symm

/-- Pointwise equality modulo two lifts to a sum over a finite type. -/
theorem fintype_sum_mod_two_congr {α : Type*} [Fintype α] (f g : α → ℕ)
    (h : ∀ x, f x % 2 = g x % 2) :
    (∑ x, f x) % 2 = (∑ x, g x) % 2 := by
  simpa using finset_sum_mod_two_congr (Finset.univ : Finset α) f g
    (fun x _ => h x)

/-- If every symmetric off-diagonal pair contributes an even amount, a finite double sum has the
same parity as its diagonal. -/
theorem finset_sum_sum_mod_two_eq_diag_of_pair_add_mod_two_eq_zero {α : Type*}
    (s : Finset α) (f : α → α → ℕ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (f a b + f b a) % 2 = 0) :
    (∑ a ∈ s, ∑ b ∈ s, f a b) % 2 = (∑ a ∈ s, f a a) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpairS : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (f x y + f y x) % 2 = 0 := by
        intro x hx y hy hxy
        exact hpair x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have ih' := ih hpairS
      have hcross : (∑ b ∈ s, (f a b + f b a)) % 2 = 0 := by
        have h := finset_sum_mod_two_congr s (fun b => f a b + f b a) (fun _ => 0)
          (fun b hb => by
            have hab : a ≠ b := by
              intro hab
              apply ha
              simpa [hab] using hb
            simpa using hpair a (Finset.mem_insert_self a s) b
              (Finset.mem_insert_of_mem hb) hab)
        simpa using h
      have hsplit :
          (∑ x ∈ insert a s, ∑ y ∈ insert a s, f x y) =
            f a a + (∑ b ∈ s, (f a b + f b a)) +
              ∑ x ∈ s, ∑ y ∈ s, f x y := by
        simp [Finset.sum_insert, ha, Finset.sum_add_distrib]
        ac_rfl
      have hdiag :
          (∑ x ∈ insert a s, f x x) = f a a + ∑ x ∈ s, f x x := by
        rw [Finset.sum_insert ha]
      rw [hsplit, hdiag]
      calc
        (f a a + (∑ b ∈ s, (f a b + f b a)) +
            ∑ x ∈ s, ∑ y ∈ s, f x y) % 2 =
          ((f a a + (∑ b ∈ s, (f a b + f b a))) % 2 +
            (∑ x ∈ s, ∑ y ∈ s, f x y) % 2) % 2 := by
              simpa only [Nat.mod_mod] using
                Nat.add_mod
                  (f a a + (∑ b ∈ s, (f a b + f b a)))
                  (∑ x ∈ s, ∑ y ∈ s, f x y) 2
        _ = (((f a a % 2 + (∑ b ∈ s, (f a b + f b a)) % 2) % 2) +
            (∑ x ∈ s, ∑ y ∈ s, f x y) % 2) % 2 := by
              simpa only [Nat.mod_mod] using congrArg
                (fun z : ℕ =>
                  (z + (∑ x ∈ s, ∑ y ∈ s, f x y) % 2) % 2)
                (Nat.add_mod (f a a) (∑ b ∈ s, (f a b + f b a)) 2)
        _ = (((f a a % 2 + 0) % 2) + (∑ x ∈ s, f x x) % 2) % 2 := by
              rw [hcross, ih']
        _ = (f a a + ∑ x ∈ s, f x x) % 2 := by
              simp only [Nat.add_zero, Nat.mod_mod]
              exact (Nat.add_mod (f a a) (∑ x ∈ s, f x x) 2).symm

/-- Finite-type form of `finset_sum_sum_mod_two_eq_diag_of_pair_add_mod_two_eq_zero`. -/
theorem fintype_sum_sum_mod_two_eq_diag_of_pair_add_mod_two_eq_zero {α : Type*}
    [Fintype α] (f : α → α → ℕ)
    (hpair : ∀ a b, a ≠ b → (f a b + f b a) % 2 = 0) :
    (∑ a, ∑ b, f a b) % 2 = (∑ a, f a a) % 2 := by
  simpa using finset_sum_sum_mod_two_eq_diag_of_pair_add_mod_two_eq_zero
    (Finset.univ : Finset α) f (fun a _ b _ hab => hpair a b hab)

end BlochDeDominicis
end Common
end SecondQuantization
