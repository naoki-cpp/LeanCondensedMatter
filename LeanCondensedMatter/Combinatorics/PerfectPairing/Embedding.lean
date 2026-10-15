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
  change Crosses (e p.1.1, e p.1.2) (e q.1.1, e q.1.2) ↔ Crosses p.1 q.1
  exact crosses_map_iff e e.strictMono p.1.1 p.1.2 q.1.1 q.1.2

/-- A normalized pair whose first endpoint lies in the range of a partner-preserving
order embedding comes from a unique local normalized pair. This is the image
characterization of the pairing restriction, without a cardinality argument. -/
theorem Pairing.exists_normalizedPairEmbedding_eq_of_firstEndpoint
    {n m : ℕ} (small : Pairing n) (big : Pairing m)
    (e : Fin (2 * n) ↪o Fin (2 * m))
    (hpartner : ∀ i, big.partner (e i) = e (small.partner i))
    (pr : big.NormalizedPair)
    (hfirst : ∃ i, e i = pr.1.1) :
    ∃ q : small.NormalizedPair,
      small.normalizedPairEmbedding big e hpartner q = pr := by
  obtain ⟨a, ha⟩ := hfirst
  have hpr := (big.mem_pairs_iff pr.1.1 pr.1.2).mp pr.2
  have hb : e (small.partner a) = pr.1.2 := by
    calc
      e (small.partner a) = big.partner (e a) := (hpartner a).symm
      _ = big.partner pr.1.1 := by rw [ha]
      _ = pr.1.2 := hpr.2
  have hab : a < small.partner a := e.lt_iff_lt.mp (by rw [ha, hb]; exact hpr.1)
  refine ⟨⟨(a, small.partner a), (small.mem_pairs_iff a (small.partner a)).mpr
    ⟨hab, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext ha hb

end Combinatorics
