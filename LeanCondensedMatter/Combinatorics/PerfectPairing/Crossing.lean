import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

set_option linter.style.header false

/-!
# Crossings and crossing counts

Two normalized pairs `(a, b)` and `(c, d)` cross when `a < c < b < d`. The canonical public
crossing representation uses `Pairing.NormalizedPair`; raw pairs with membership witnesses are
kept only as a private proof device.
-/

namespace Combinatorics

/-- The normalized pair `(a, b)` crosses `(c, d)` when `a < c < b < d`. -/
def Crosses {n : ℕ} (left right : Fin (2 * n) × Fin (2 * n)) : Prop :=
  left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2

instance decidableCrosses {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) : Decidable (Crosses left right) :=
  inferInstanceAs (Decidable (
    left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2))

/-- The two oriented crossing indicators are disjoint, so their sum counts geometric crossings
without double counting. -/
theorem crossesIndicator_add {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) :
    (if Crosses left right then (1 : ℕ) else 0) +
      (if Crosses right left then 1 else 0) =
        (if Crosses left right ∨ Crosses right left then 1 else 0) := by
  by_cases hleft : Crosses left right
  · have hright : ¬ Crosses right left := fun h => lt_asymm hleft.1 h.1
    simp [hleft, hright]
  · simp [hleft]

/-- A strictly monotone embedding preserves and reflects the crossing relation. -/
theorem crosses_map_iff {n m : ℕ} (f : Fin (2 * n) → Fin (2 * m)) (hf : StrictMono f)
    (a b c e : Fin (2 * n)) :
    Crosses (f a, f b) (f c, f e) ↔ Crosses (a, b) (c, e) := by
  constructor
  · rintro ⟨hac, hcb, hbe⟩
    refine ⟨?_, ?_, ?_⟩
    · apply lt_of_not_ge
      intro hca
      exact (not_lt_of_ge (hf.monotone hca)) hac
    · apply lt_of_not_ge
      intro hbc
      exact (not_lt_of_ge (hf.monotone hbc)) hcb
    · apply lt_of_not_ge
      intro heb
      exact (not_lt_of_ge (hf.monotone heb)) hbe
  · rintro ⟨hac, hcb, hbe⟩
    exact ⟨hf hac, hf hcb, hf hbe⟩

/-- A crossing-preserving equivalence of finite pair families preserves the double crossing count. -/
theorem sum_sum_crosses_eq_of_equiv {n m : ℕ} {A B : Type*}
    [Fintype A] [Fintype B]
    (pairA : A → Fin (2 * n) × Fin (2 * n))
    (pairB : B → Fin (2 * m) × Fin (2 * m))
    (e : A ≃ B)
    (hcross : ∀ p q, Crosses (pairA p) (pairA q) ↔
      Crosses (pairB (e p)) (pairB (e q))) :
    (∑ p : A, ∑ q : A, if Crosses (pairA p) (pairA q) then 1 else 0) =
      ∑ p : B, ∑ q : B, if Crosses (pairB p) (pairB q) then 1 else 0 := by
  classical
  refine Fintype.sum_equiv e
    (fun p : A => ∑ q : A, if Crosses (pairA p) (pairA q) then 1 else 0)
    (fun p : B => ∑ q : B, if Crosses (pairB p) (pairB q) then 1 else 0) ?_
  intro p
  refine Fintype.sum_equiv e
    (fun q : A => if Crosses (pairA p) (pairA q) then 1 else 0)
    (fun q : B => if Crosses (pairB (e p)) (pairB q) then 1 else 0) ?_
  intro q
  exact if_congr (hcross p q) rfl rfl

/-- The number of geometric crossings. -/
def Pairing.crossingCount {n : ℕ} (pairing : Pairing n) : ℕ :=
  ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
    Crosses pairPair.1 pairPair.2).card

/-- `crossingCount` as a `0`-or-`1` sum over all ordered normalized-pair pairs. -/
theorem Pairing.crossingCount_eq_sum_crosses {n : ℕ} (pairing : Pairing n) :
    pairing.crossingCount =
      ∑ x : pairing.NormalizedPair × pairing.NormalizedPair,
        if Crosses x.1.1 x.2.1 then 1 else 0 := by
  classical
  rw [Pairing.crossingCount, ← Finset.sum_boole]
  simp only [Finset.sum_product, Fintype.sum_prod_type]
  calc
    (∑ p ∈ pairing.pairs, ∑ q ∈ pairing.pairs,
      if Crosses p q then 1 else 0) =
        ∑ p ∈ pairing.pairs.attach, ∑ q ∈ pairing.pairs.attach,
          if Crosses p.1 q.1 then 1 else 0 := by
      symm
      rw [Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_attach]
    _ = _ := by rw [Finset.attach_eq_univ]

/-- The number of pairs crossing `firstPair`. -/
def Pairing.crossingsWithFirstPair {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.pairs.filter fun p => Crosses pairing.firstPair p).card

theorem not_crosses_firstPair {n : ℕ} (pairing : Pairing (n + 1))
    (p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))) : ¬ Crosses p pairing.firstPair := by
  rintro ⟨h1, -, -⟩
  exact absurd h1 (by simp [Pairing.firstPair])

theorem not_crosses_self {n : ℕ} (p : Fin (2 * n) × Fin (2 * n)) : ¬ Crosses p p := by
  rintro ⟨h, -, -⟩
  exact absurd h (lt_irrefl _)

end Combinatorics
