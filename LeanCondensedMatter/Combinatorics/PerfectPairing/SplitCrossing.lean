import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.SplitNormalizedPairs
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Crossings under a binary position splitting

The crossing count of an assembled pairing decomposes into within-sector and between-sector
contributions. Strictly increasing sector embeddings identify the within-sector counts with
the local pairing counts. The between-sector parity is the position-inversion parity even when
the splitting reverses transported pairs.
-/

namespace Combinatorics

variable {α β γ : Type*}
  [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [Fintype γ] [LinearOrder γ]

/-- Crossings between the two independent sectors of an assembled pairing.
Both orientations are counted because `crossingCount` uses oriented pairs. -/
noncomputable def PairingOn.ofSplitInterSectorCrossingCount
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) : ℕ :=
  let emb := PairingOn.ofSplitNormalizedPairEquiv e P Q
  (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
      if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
    ∑ q : Q.NormalizedPair, ∑ p : P.NormalizedPair,
      if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0

/-- The only residual crossing parity of a binary split is the parity of
the inter-sector position inversions, independently of the pairing chosen
inside either half. -/
theorem PairingOn.ofSplitInterSectorCrossingCount_mod_two_eq_positionInversions
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (PairingOn.ofSplitInterSectorCrossingCount e P Q) % 2 =
      (∑ i : α, ∑ j : β,
        if e (Sum.inr j) < e (Sum.inl i) then 1 else 0) % 2 := by
  classical
  let emb := PairingOn.ofSplitNormalizedPairEquiv e P Q
  have hsum :
      PairingOn.ofSplitInterSectorCrossingCount e P Q =
        ∑ x : P.NormalizedPair × Q.NormalizedPair,
          if Crosses (emb (Sum.inl x.1)).1 (emb (Sum.inr x.2)).1 ∨
            Crosses (emb (Sum.inr x.2)).1 (emb (Sum.inl x.1)).1 then 1 else 0 := by
    exact sum_sum_crosses_oriented_add
      (fun p : P.NormalizedPair => (emb (Sum.inl p)).1)
      (fun q : Q.NormalizedPair => (emb (Sum.inr q)).1)
  rw [hsum]
  exact (PairingOn.ofSplit e P Q).sum_geometricCrossings_mod_two_eq_positionInversions
    (fun p => emb (Sum.inl p)) (fun q => emb (Sum.inr q))
    (fun p q h => by cases emb.injective h)
    P.pairEndpointEquiv Q.pairEndpointEquiv
    (fun i => e (Sum.inl i)) (fun j => e (Sum.inr j))
    (fun p => PairingOn.ofSplitNormalizedPairEquiv_pair_eq_or_swap e P Q (Sum.inl p))
    (fun q => PairingOn.ofSplitNormalizedPairEquiv_pair_eq_or_swap e P Q (Sum.inr q))

/-- With strictly increasing embeddings of both sectors, the sole extra
crossing count is the explicitly identified inter-sector contribution. -/
theorem PairingOn.ofSplit_crossingCount_eq_left_add_right_add_inter
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (hleft : StrictMono (fun i : α => e (Sum.inl i)))
    (hright : StrictMono (fun i : β => e (Sum.inr i))) :
    (PairingOn.ofSplit e P Q).crossingCount =
      P.crossingCount + Q.crossingCount +
        PairingOn.ofSplitInterSectorCrossingCount e P Q := by
  have hdecomp :
      (PairingOn.ofSplit e P Q).crossingCount =
        (∑ p : P.NormalizedPair, ∑ q : P.NormalizedPair,
          if Crosses
              (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
              (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl q)).1
          then 1 else 0) +
        (∑ p : Q.NormalizedPair, ∑ q : Q.NormalizedPair,
          if Crosses
              (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1
              (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1
          then 1 else 0) +
        PairingOn.ofSplitInterSectorCrossingCount e P Q := by
    classical
    let emb := PairingOn.ofSplitNormalizedPairEquiv e P Q
    have hsum :
        (PairingOn.ofSplit e P Q).crossingCount =
          ∑ xy : (P.NormalizedPair ⊕ Q.NormalizedPair) ×
              (P.NormalizedPair ⊕ Q.NormalizedPair),
            if Crosses (emb xy.1).1 (emb xy.2).1 then 1 else 0 := by
      rw [PairingOn.crossingCount_eq_sum_crosses]
      exact (Equiv.sum_comp (Equiv.prodCongr emb emb)
        (fun xy : (PairingOn.ofSplit e P Q).NormalizedPair ×
            (PairingOn.ofSplit e P Q).NormalizedPair =>
          if Crosses xy.1.1 xy.2.1 then (1 : ℕ) else 0)).symm
    rw [hsum, Fintype.sum_prod_type, Fintype.sum_sum_type]
    simp_rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
    unfold PairingOn.ofSplitInterSectorCrossingCount
    dsimp [emb]
    omega
  rw [hdecomp,
    P.sum_sum_crosses_map_eq_crossingCount
      (fun i => e (Sum.inl i)) hleft
      (fun p => (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1) (Equiv.refl _)
      (fun p => PairingOn.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inl p)
        (hleft (P.pairs_normalized p.2))),
    Q.sum_sum_crosses_map_eq_crossingCount
      (fun i => e (Sum.inr i)) hright
      (fun p => (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1) (Equiv.refl _)
      (fun p => PairingOn.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inr p)
        (hright (Q.pairs_normalized p.2)))]

end Combinatorics
