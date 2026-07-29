import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.Common.FinsetProduct

set_option linter.style.header false

/-!
# Crossings, `crossingCount`, and `firstPair`

Two normalized pairs `(a, b)` and `(c, d)` cross when `a < c < b < d` (`Crosses`); `crossingCount`
counts these across a pairing's own `pairs`. The statistics-dependent exchange weight
`ζ ^ crossingCount` itself — `ζ = +1` for bosons and `ζ = -1` for fermions — is *not* defined here;
see `Common/Thermal/BlochDeDominicis/PairingWeight.lean`.

`Pairing.firstPair` is the pair containing position `0`; `crossingsWithFirstPair` counts pairs
crossing it. `PerfectPairing/CrossingEraseZero.lean` relates both to
`Pairing.eraseZeroPair`/`interveningPositionCount`.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- The normalized pair `(a, b)` crosses `(c, d)` when `a < c < b < d`. -/
def Crosses {n : ℕ} (left right : Fin (2 * n) × Fin (2 * n)) : Prop :=
  left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2

instance decidableCrosses {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) : Decidable (Crosses left right) :=
  inferInstanceAs (Decidable (
    left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2))

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

/-- The number of geometric crossings. `Crosses` fixes the order of the left endpoints, so each
crossing is counted exactly once. -/
def Pairing.crossingCount {n : ℕ} (pairing : Pairing n) : ℕ :=
  ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
    Crosses pairPair.1 pairPair.2).card

/-- The finite type of ordered pair-of-pairs that contribute to `crossingCount`. -/
abbrev Pairing.CrossingPair {n : ℕ} (pairing : Pairing n) :=
  {pairPair :
      (Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n)) //
    pairPair.1 ∈ pairing.pairs ∧ pairPair.2 ∈ pairing.pairs ∧
      Crosses pairPair.1 pairPair.2}

/-- `crossingCount` is the cardinality of the type of crossing pair-of-pairs. -/
theorem Pairing.crossingCount_eq_card_crossingPair {n : ℕ} (pairing : Pairing n) :
    pairing.crossingCount = Fintype.card pairing.CrossingPair := by
  rw [Pairing.crossingCount]
  symm
  exact Fintype.card_of_subtype
    (p := fun pairPair :
        (Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n)) =>
      pairPair.1 ∈ pairing.pairs ∧ pairPair.2 ∈ pairing.pairs ∧
        Crosses pairPair.1 pairPair.2)
    ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
      Crosses pairPair.1 pairPair.2)
    (fun pairPair => by
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
      constructor
      · rintro ⟨⟨hleft, hright⟩, hcross⟩
        exact ⟨hleft, hright, hcross⟩
      · rintro ⟨hleft, hright, hcross⟩
        exact ⟨⟨hleft, hright⟩, hcross⟩)

/-- The pair containing position `0`, i.e. `(0, partner 0)`. -/
def Pairing.firstPair {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * (n + 1)) × Fin (2 * (n + 1)) :=
  (0, pairing.partner 0)

theorem Pairing.firstPair_mem_pairs {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.firstPair ∈ pairing.pairs := by
  apply (pairing.mem_pairs_iff 0 (pairing.partner 0)).2
  exact ⟨lt_of_le_of_ne (Fin.zero_le _) (Ne.symm (pairing.partner_ne 0)), rfl⟩

/-- The number of pairs (other than `firstPair`) crossing `firstPair`. -/
def Pairing.crossingsWithFirstPair {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.pairs.filter fun p => Crosses pairing.firstPair p).card

theorem not_crosses_firstPair {n : ℕ} (pairing : Pairing (n + 1))
    (p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))) : ¬ Crosses p pairing.firstPair := by
  rintro ⟨h1, -, -⟩
  exact absurd h1 (by simp [Pairing.firstPair])

theorem not_crosses_self {n : ℕ} (p : Fin (2 * n) × Fin (2 * n)) : ¬ Crosses p p := by
  rintro ⟨h, -, -⟩
  exact absurd h (lt_irrefl _)

/-- A crossing-count as a product-filter card decomposes into a sum over the left endpoint —
`Finset.card_filter_product_eq_sum_card_filter` specialized to `Crosses`. -/
theorem card_filter_crosses_product_eq_sum {n : ℕ} (T : Finset (Fin (2 * n) × Fin (2 * n))) :
    ((T.product T).filter (fun pp => Crosses pp.1 pp.2)).card =
      ∑ p ∈ T, (T.filter (fun q => Crosses p q)).card :=
  Finset.card_filter_product_eq_sum_card_filter T Crosses

end BlochDeDominicis
end Common
end SecondQuantization
