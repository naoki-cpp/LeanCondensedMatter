import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Crossings, `crossingCount`, and `firstPair`

Two normalized pairs `(a, b)` and `(c, d)` cross when `a < c < b < d` (`Crosses`); `crossingCount`
counts these across a pairing's own `pairs`. The statistics-dependent exchange weight
`ζ ^ crossingCount` itself — `ζ = +1` for bosons, `ζ = -1` for fermions — is *not* defined here; see
`Common/BlochDeDominicis/PairingWeight.lean`.

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

/-- The number of geometric crossings.  `Crosses` fixes the order of the left endpoints, so each
crossing is counted exactly once. -/
def Pairing.crossingCount {n : ℕ} (pairing : Pairing n) : ℕ :=
  ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
    Crosses pairPair.1 pairPair.2).card

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

/-- A crossing-count as a product-filter card decomposes into a sum over the left endpoint. -/
theorem card_filter_crosses_product_eq_sum {n : ℕ} (T : Finset (Fin (2 * n) × Fin (2 * n))) :
    ((T.product T).filter (fun pp => Crosses pp.1 pp.2)).card =
      ∑ p ∈ T, (T.filter (fun q => Crosses p q)).card := by
  classical
  have hmaps : Set.MapsTo
      (Prod.fst : (Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n)) →
        Fin (2 * n) × Fin (2 * n))
      (((T.product T).filter (fun pp => Crosses pp.1 pp.2) :
        Finset ((Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n)))) : Set _)
      (T : Set (Fin (2 * n) × Fin (2 * n))) := by
    intro pp hpp
    simp only [Finset.coe_filter, Finset.product_eq_sprod, Finset.mem_product,
      Set.mem_setOf_eq] at hpp
    exact hpp.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro p _
  have himg :
      ((T.product T).filter (fun pp => Crosses pp.1 pp.2)).filter (fun pp => pp.1 = p) =
        (T.filter (fun q => Crosses p q)).image (fun q => (p, q)) := by
    ext pp
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨-, h2⟩, hcross⟩, rfl⟩
      exact ⟨pp.2, ⟨h2, hcross⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hcross⟩, rfl⟩
      exact ⟨⟨⟨‹p ∈ T›, hq⟩, hcross⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun a b h => by simpa using h]

end BlochDeDominicis
end Common
end SecondQuantization
