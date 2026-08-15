import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing

set_option linter.style.header false

/-!
# Embeddings of perfect pairings

This module packages the common transport pattern for perfect pairings along a strictly
order-preserving embedding of their ordered positions.  When the embedding intertwines partner
maps, normalized pair membership is preserved and reflected, normalized pairs embed canonically,
and crossing geometry is unchanged.
-/

namespace Combinatorics

/-- If an order embedding intertwines two pairing partner maps, mapping both endpoints preserves and
reflects normalized pair membership. -/
theorem Pairing.mem_pairs_map_iff {n m : ℕ}
    (small : Pairing n) (big : Pairing m)
    (e : Fin (2 * n) ↪o Fin (2 * m))
    (hpartner : ∀ i, big.partner (e i) = e (small.partner i))
    (a b : Fin (2 * n)) :
    (e a, e b) ∈ big.pairs ↔ (a, b) ∈ small.pairs := by
  rw [Pairing.mem_pairs_iff, Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hab, hp⟩
    refine ⟨e.lt_iff_lt.mp hab, ?_⟩
    apply e.injective
    calc
      e (small.partner a) = big.partner (e a) := (hpartner a).symm
      _ = e b := hp
  · rintro ⟨hab, hp⟩
    refine ⟨e.lt_iff_lt.mpr hab, ?_⟩
    rw [hpartner a, hp]

/-- A partner-intertwining order embedding sends normalized pairs injectively to normalized pairs. -/
noncomputable def Pairing.normalizedPairEmbedding {n m : ℕ}
    (small : Pairing n) (big : Pairing m)
    (e : Fin (2 * n) ↪o Fin (2 * m))
    (hpartner : ∀ i, big.partner (e i) = e (small.partner i)) :
    small.NormalizedPair ↪ big.NormalizedPair where
  toFun pr :=
    ⟨(e pr.1.1, e pr.1.2),
      (small.mem_pairs_map_iff big e hpartner pr.1.1 pr.1.2).2 pr.2⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply e.injective
      exact congrArg (fun z => z.1.1) hpq
    · apply e.injective
      exact congrArg (fun z => z.1.2) hpq

@[simp]
theorem Pairing.normalizedPairEmbedding_apply {n m : ℕ}
    (small : Pairing n) (big : Pairing m)
    (e : Fin (2 * n) ↪o Fin (2 * m))
    (hpartner : ∀ i, big.partner (e i) = e (small.partner i))
    (pr : small.NormalizedPair) :
    (small.normalizedPairEmbedding big e hpartner pr).1 =
      (e pr.1.1, e pr.1.2) :=
  rfl

/-- A partner-intertwining order embedding preserves and reflects crossings between normalized
pairs. -/
theorem Pairing.normalizedPairEmbedding_crosses_iff {n m : ℕ}
    (small : Pairing n) (big : Pairing m)
    (e : Fin (2 * n) ↪o Fin (2 * m))
    (hpartner : ∀ i, big.partner (e i) = e (small.partner i))
    (p q : small.NormalizedPair) :
    Crosses (small.normalizedPairEmbedding big e hpartner p).1
        (small.normalizedPairEmbedding big e hpartner q).1 ↔
      Crosses p.1 q.1 := by
  rw [small.normalizedPairEmbedding_apply big e hpartner,
    small.normalizedPairEmbedding_apply big e hpartner]
  exact crosses_map_iff e e.strictMono p.1.1 p.1.2 q.1.1 q.1.2

end Combinatorics
