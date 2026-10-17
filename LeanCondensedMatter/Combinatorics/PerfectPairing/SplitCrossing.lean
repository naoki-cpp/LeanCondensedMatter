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

variable {a b n : ℕ}

/-- The ordered crossing count internal to the left part of an assembled
pairing is its standalone crossing count. Inter-part crossings are excluded. -/
private theorem Pairing.ofSplitNormalizedPairEquiv_inl_crossingCount_eq
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hmono : StrictMono (fun i : Fin (2 * a) => e (Sum.inl i))) :
    (∑ p : P.NormalizedPair, ∑ q : P.NormalizedPair,
      if Crosses
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl q)).1
      then 1 else 0) = P.crossingCount := by
  classical
  rw [P.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv
    (fun p : P.NormalizedPair =>
      (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1)
    (fun p : P.NormalizedPair => p.1) (Equiv.refl _)
    (by
      intro p q
      have hp :=
        Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inl p)
          (hmono (P.pairs_normalized p.2))
      have hq :=
        Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inl q)
          (hmono (P.pairs_normalized q.2))
      rw [hp, hq]
      exact crosses_map_iff (fun i => e (Sum.inl i)) hmono
        p.1.1 p.1.2 q.1.1 q.1.2)

/-- The ordered crossing count internal to the right part of an
assembled pairing is its standalone crossing count. Inter-part crossings remain separate. -/
private theorem Pairing.ofSplitNormalizedPairEquiv_inr_crossingCount_eq
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hmono : StrictMono (fun i : Fin (2 * b) => e (Sum.inr i))) :
    (∑ p : Q.NormalizedPair, ∑ q : Q.NormalizedPair,
      if Crosses
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1
      then 1 else 0) = Q.crossingCount := by
  classical
  rw [Q.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv
    (fun p : Q.NormalizedPair =>
      (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1)
    (fun p : Q.NormalizedPair => p.1) (Equiv.refl _)
    (by
      intro p q
      have hp :=
        Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inr p)
          (hmono (Q.pairs_normalized p.2))
      have hq :=
        Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inr q)
          (hmono (Q.pairs_normalized q.2))
      rw [hp, hq]
      exact crosses_map_iff (fun i => e (Sum.inr i)) hmono
        p.1.1 p.1.2 q.1.1 q.1.2)

/-- Crossings between the two independent sectors of an assembled pairing.
Both orientations are counted because `crossingCount` uses oriented pairs. -/
noncomputable def Pairing.ofSplitInterSectorCrossingCount
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) : ℕ :=
  let emb := Pairing.ofSplitNormalizedPairEquiv e P Q
  (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
      if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
    ∑ q : Q.NormalizedPair, ∑ p : P.NormalizedPair,
      if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0

/-- The parity of crossings between the two halves of an assembled pairing
is the parity of the four endpoint-order inversions for each cross-sector
pair of normalized pairs. The two crossing orientations are both counted;
no order-preservation hypothesis is needed on either half. -/
private theorem Pairing.ofSplitInterSectorCrossingCount_mod_two_eq_pairEndpointInversionCount
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplitInterSectorCrossingCount e P Q) % 2 =
      (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
        pairEndpointInversionCount
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1) % 2 := by
  classical
  let emb := Pairing.ofSplitNormalizedPairEquiv e P Q
  have hpoint (p : P.NormalizedPair) (q : Q.NormalizedPair) :
      Nat.ModEq 2
        ((if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
          (if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0))
        (pairEndpointInversionCount
          (emb (Sum.inl p)).1 (emb (Sum.inr q)).1) := by
    have hne : emb (Sum.inl p) ≠ emb (Sum.inr q) := by
      intro h
      have hsum := emb.injective h
      cases hsum
    have hEnds := (Pairing.ofSplit e P Q).normalizedPair_endpoints_ne_of_ne
      (emb (Sum.inl p)) (emb (Sum.inr q)) hne
    have hcross := pairEndpointInversionCount_mod_two_eq_crossesIndicator
      (emb (Sum.inl p)).1 (emb (Sum.inr q)).1
      ((Pairing.ofSplit e P Q).pairs_normalized (emb (Sum.inl p)).2)
      ((Pairing.ofSplit e P Q).pairs_normalized (emb (Sum.inr q)).2)
      hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2
    change _ % 2 = _ % 2
    rw [crossesIndicator_add, hcross]
    split_ifs <;> decide
  have hsum :
      Pairing.ofSplitInterSectorCrossingCount e P Q =
        ∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
          ((if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
            (if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0)) := by
    change
      (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
        if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
      (∑ q : Q.NormalizedPair, ∑ p : P.NormalizedPair,
        if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0) = _
    rw [Finset.sum_comm (f := fun q : Q.NormalizedPair =>
      fun p : P.NormalizedPair =>
        if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_add_distrib]
  rw [hsum]
  simpa only [Nat.ModEq] using (Nat.ModEq.sum (n := 2)
    (s := (Finset.univ : Finset P.NormalizedPair))
    (f := fun p => ∑ q : Q.NormalizedPair,
      ((if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
        (if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0)))
    (g := fun p => ∑ q : Q.NormalizedPair,
      pairEndpointInversionCount
        (emb (Sum.inl p)).1 (emb (Sum.inr q)).1)
    (fun p _ => Nat.ModEq.sum (n := 2)
      (s := (Finset.univ : Finset Q.NormalizedPair))
      (f := fun q =>
        (if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
          (if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0))
      (g := fun q => pairEndpointInversionCount
        (emb (Sum.inl p)).1 (emb (Sum.inr q)).1)
      (fun q _ => hpoint p q)))

/-- A cross-sector pair-endpoint inversion counts all four comparisons
between the transported local endpoints. This remains true when ambient
normalization reverses either transported pair. -/
private theorem Pairing.ofSplit_pairEndpointInversionCount_eq_sum_localEndpoints
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (p : P.NormalizedPair) (q : Q.NormalizedPair) :
    pairEndpointInversionCount
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1 =
      ∑ i : Fin 2, ∑ j : Fin 2,
        if e (Sum.inr (Q.pairEndpointEquiv (q, j))) <
            e (Sum.inl (P.pairEndpointEquiv (p, i))) then 1 else 0 := by
  rcases Pairing.ofSplitNormalizedPairEquiv_pair_eq_or_swap
    e P Q (Sum.inl p) with hp | hp <;>
  rcases Pairing.ofSplitNormalizedPairEquiv_pair_eq_or_swap
    e P Q (Sum.inr q) with hq | hq
  all_goals
    simp only [hp, hq, Pairing.pairEndpointEquiv_apply]
    simp only [Fin.sum_univ_two, Pairing.pairEndpoint_zero, Pairing.pairEndpoint_one,
      pairEndpointInversionCount]
    ac_rfl

/-- The total of pairwise cross-sector endpoint inversions is exactly the
number of positions from the right half that precede positions from the left
half in an arbitrary binary position splitting. Both pair orientations and
all pair enumeration choices disappear under endpoint reindexing. -/
private theorem Pairing.ofSplit_sum_pairEndpointInversionCount_eq_positionInversions
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
      pairEndpointInversionCount
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1) =
      ∑ i : Fin (2 * a), ∑ j : Fin (2 * b),
        if e (Sum.inr j) < e (Sum.inl i) then 1 else 0 := by
  classical
  have hlocal :
      (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
        pairEndpointInversionCount
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1) =
        ∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
          ∑ i : Fin 2, ∑ j : Fin 2,
            if e (Sum.inr (Q.pairEndpointEquiv (q, j))) <
                e (Sum.inl (P.pairEndpointEquiv (p, i))) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    exact Pairing.ofSplit_pairEndpointInversionCount_eq_sum_localEndpoints e P Q p q
  rw [hlocal]
  calc
    (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
      ∑ i : Fin 2, ∑ j : Fin 2,
        if e (Sum.inr (Q.pairEndpointEquiv (q, j))) <
            e (Sum.inl (P.pairEndpointEquiv (p, i))) then 1 else 0) =
        ∑ x : (P.NormalizedPair × Q.NormalizedPair) × (Fin 2 × Fin 2),
          if e (Sum.inr (Q.pairEndpointEquiv (x.1.2, x.2.2))) <
              e (Sum.inl (P.pairEndpointEquiv (x.1.1, x.2.1))) then 1 else 0 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ x : Fin (2 * a) × Fin (2 * b),
          if e (Sum.inr x.2) < e (Sum.inl x.1) then 1 else 0 := by
      refine Fintype.sum_equiv
        ((Equiv.prodProdProdComm _ _ _ _).trans
          (Equiv.prodCongr P.pairEndpointEquiv Q.pairEndpointEquiv))
        _ _ ?_
      intro x
      rfl
    _ = _ := by rw [Fintype.sum_prod_type]

/-- The only residual crossing parity of a binary split is the parity of
the inter-sector position inversions, independently of the pairing chosen
inside either half. -/
theorem Pairing.ofSplitInterSectorCrossingCount_mod_two_eq_positionInversions
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplitInterSectorCrossingCount e P Q) % 2 =
      (∑ i : Fin (2 * a), ∑ j : Fin (2 * b),
        if e (Sum.inr j) < e (Sum.inl i) then 1 else 0) % 2 := by
  rw [Pairing.ofSplitInterSectorCrossingCount_mod_two_eq_pairEndpointInversionCount,
    Pairing.ofSplit_sum_pairEndpointInversionCount_eq_positionInversions]

/-- With strictly increasing embeddings of both sectors, the sole extra
crossing count is the explicitly identified inter-sector contribution. -/
theorem Pairing.ofSplit_crossingCount_eq_left_add_right_add_inter
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hleft : StrictMono (fun i : Fin (2 * a) => e (Sum.inl i)))
    (hright : StrictMono (fun i : Fin (2 * b) => e (Sum.inr i))) :
    (Pairing.ofSplit e P Q).crossingCount =
      P.crossingCount + Q.crossingCount +
        Pairing.ofSplitInterSectorCrossingCount e P Q := by
  have hdecomp :
      (Pairing.ofSplit e P Q).crossingCount =
        (∑ p : P.NormalizedPair, ∑ q : P.NormalizedPair,
          if Crosses
              (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
              (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl q)).1
          then 1 else 0) +
        (∑ p : Q.NormalizedPair, ∑ q : Q.NormalizedPair,
          if Crosses
              (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1
              (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1
          then 1 else 0) +
        Pairing.ofSplitInterSectorCrossingCount e P Q := by
    classical
    let emb := Pairing.ofSplitNormalizedPairEquiv e P Q
    have hsum :
        (Pairing.ofSplit e P Q).crossingCount =
          ∑ xy : (P.NormalizedPair ⊕ Q.NormalizedPair) ×
              (P.NormalizedPair ⊕ Q.NormalizedPair),
            if Crosses (emb xy.1).1 (emb xy.2).1 then 1 else 0 := by
      rw [Pairing.crossingCount_eq_sum_crosses]
      exact (Equiv.sum_comp (Equiv.prodCongr emb emb)
        (fun xy : (Pairing.ofSplit e P Q).NormalizedPair ×
            (Pairing.ofSplit e P Q).NormalizedPair =>
          if Crosses xy.1.1 xy.2.1 then (1 : ℕ) else 0)).symm
    rw [hsum, Fintype.sum_prod_type, Fintype.sum_sum_type]
    simp_rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
    unfold Pairing.ofSplitInterSectorCrossingCount
    dsimp [emb]
    omega
  rw [hdecomp,
    Pairing.ofSplitNormalizedPairEquiv_inl_crossingCount_eq e P Q hleft,
    Pairing.ofSplitNormalizedPairEquiv_inr_crossingCount_eq e P Q hright]

end Combinatorics
