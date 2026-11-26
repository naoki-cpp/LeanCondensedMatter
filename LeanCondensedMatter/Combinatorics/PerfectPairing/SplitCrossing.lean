import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.SplitNormalizedPairs
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
import Mathlib.Algebra.BigOperators.ModEq

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

/-- A strictly increasing position embedding preserves the double crossing count of
normalized pairs when their endpoints are transported in their normalized order. -/
private theorem PairingOn.sum_sum_crosses_map_eq_crossingCount {δ ε : Type*} [Fintype δ] [LinearOrder δ] [LinearOrder ε]
    (R : PairingOn δ) (f : δ → ε) (hmono : StrictMono f)
    (pairImage : R.NormalizedPair → ε × ε)
    (himage : ∀ p : R.NormalizedPair,
      pairImage p = (f p.1.1, f p.1.2)) :
    (∑ p : R.NormalizedPair, ∑ q : R.NormalizedPair,
      if Crosses (pairImage p) (pairImage q) then 1 else 0) = R.crossingCount := by
  classical
  rw [R.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv pairImage (fun p : R.NormalizedPair => p.1)
    (Equiv.refl _) (fun p q => by
      rw [himage p, himage q]
      exact crosses_map_iff f hmono p.1.1 p.1.2 q.1.1 q.1.2)

/-- Crossings between the two independent sectors of an assembled pairing.
Both orientations are counted because `crossingCount` uses oriented pairs. -/
noncomputable def PairingOn.ofSplitInterSectorCrossingCount
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) : ℕ :=
  let emb := PairingOn.ofSplitNormalizedPairEquiv e P Q
  (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
      if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
    ∑ q : Q.NormalizedPair, ∑ p : P.NormalizedPair,
      if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0

/-- The parity of crossings between the two halves of an assembled pairing
is the parity of the four endpoint-order inversions for each cross-sector
pair of normalized pairs. The two crossing orientations are both counted;
no order-preservation hypothesis is needed on either half. -/
private theorem PairingOn.ofSplitInterSectorCrossingCount_mod_two_eq_pairEndpointInversionCount
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (PairingOn.ofSplitInterSectorCrossingCount e P Q) % 2 =
      (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
        pairEndpointInversionCount
          (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
          (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1) % 2 := by
  classical
  let emb := PairingOn.ofSplitNormalizedPairEquiv e P Q
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
    have hEnds := (PairingOn.ofSplit e P Q).normalizedPair_endpoints_ne_of_ne
      (emb (Sum.inl p)) (emb (Sum.inr q)) hne
    have hcross := pairEndpointInversionCount_mod_two_eq_crossesIndicator
      (emb (Sum.inl p)).1 (emb (Sum.inr q)).1
      ((PairingOn.ofSplit e P Q).pairs_normalized (emb (Sum.inl p)).2)
      ((PairingOn.ofSplit e P Q).pairs_normalized (emb (Sum.inr q)).2)
      hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2
    change _ % 2 = _ % 2
    rw [crossesIndicator_add, hcross]
    split_ifs <;> decide
  have hsum :
      PairingOn.ofSplitInterSectorCrossingCount e P Q =
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
private theorem PairingOn.ofSplit_pairEndpointInversionCount_eq_sum_localEndpoints
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (p : P.NormalizedPair) (q : Q.NormalizedPair) :
    pairEndpointInversionCount
        (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
        (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1 =
      ∑ i : Fin 2, ∑ j : Fin 2,
        if e (Sum.inr (Q.pairEndpointEquiv (q, j))) <
            e (Sum.inl (P.pairEndpointEquiv (p, i))) then 1 else 0 := by
  rcases PairingOn.ofSplitNormalizedPairEquiv_pair_eq_or_swap
    e P Q (Sum.inl p) with hp | hp <;>
  rcases PairingOn.ofSplitNormalizedPairEquiv_pair_eq_or_swap
    e P Q (Sum.inr q) with hq | hq
  all_goals
    simp only [hp, hq, PairingOn.pairEndpointEquiv_apply]
    simp only [Fin.sum_univ_two, pairEndpointAt_zero, pairEndpointAt_one,
      pairEndpointInversionCount]
    ac_rfl

/-- The total of pairwise cross-sector endpoint inversions is exactly the
number of positions from the right half that precede positions from the left
half in an arbitrary binary position splitting. Both pair orientations and
all pair enumeration choices disappear under endpoint reindexing. -/
private theorem PairingOn.ofSplit_sum_pairEndpointInversionCount_eq_positionInversions
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
      pairEndpointInversionCount
        (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
        (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1) =
      ∑ i : α, ∑ j : β,
        if e (Sum.inr j) < e (Sum.inl i) then 1 else 0 := by
  classical
  have hlocal :
      (∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
        pairEndpointInversionCount
          (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
          (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1) =
        ∑ p : P.NormalizedPair, ∑ q : Q.NormalizedPair,
          ∑ i : Fin 2, ∑ j : Fin 2,
            if e (Sum.inr (Q.pairEndpointEquiv (q, j))) <
                e (Sum.inl (P.pairEndpointEquiv (p, i))) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    exact PairingOn.ofSplit_pairEndpointInversionCount_eq_sum_localEndpoints e P Q p q
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
    _ = ∑ x : α × β,
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
theorem PairingOn.ofSplitInterSectorCrossingCount_mod_two_eq_positionInversions
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (PairingOn.ofSplitInterSectorCrossingCount e P Q) % 2 =
      (∑ i : α, ∑ j : β,
        if e (Sum.inr j) < e (Sum.inl i) then 1 else 0) % 2 := by
  rw [PairingOn.ofSplitInterSectorCrossingCount_mod_two_eq_pairEndpointInversionCount,
    PairingOn.ofSplit_sum_pairEndpointInversionCount_eq_positionInversions]

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
      (fun p => (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1)
      (fun p => PairingOn.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inl p)
        (hleft (P.pairs_normalized p.2))),
    Q.sum_sum_crosses_map_eq_crossingCount
      (fun i => e (Sum.inr i)) hright
      (fun p => (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1)
      (fun p => PairingOn.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inr p)
        (hright (Q.pairs_normalized p.2)))]

end Combinatorics
