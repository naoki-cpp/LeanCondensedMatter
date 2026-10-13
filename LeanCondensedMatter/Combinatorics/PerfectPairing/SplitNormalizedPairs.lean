import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Normalized pairs under a binary position splitting

Reindex normalized pair products after assembling independent pairings. Kept downstream
from the elementary splitting API to avoid making all partner-only consumers import the
normalized endpoint equivalence and its proof dependencies.
-/

namespace Combinatorics

variable {a b n : ℕ}

/-- Normalized pairs of a pairing assembled from two independent parts are precisely
the normalized pairs of those parts, tagged by their side.

The position splitting is not required to preserve the ambient order: normalization may
reverse an individual transported pair. This equivalence is the reindexing input for
factorizing products of pair contractions over an arbitrary slot shuffle. -/
noncomputable def Pairing.ofSplitNormalizedPairEquiv
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    P.NormalizedPair ⊕ Q.NormalizedPair ≃ (Pairing.ofSplit e P Q).NormalizedPair := by
  classical
  let endpointEquiv :
      (P.NormalizedPair ⊕ Q.NormalizedPair) × Fin 2 ≃
        Fin (2 * a) ⊕ Fin (2 * b) :=
    (Equiv.sumProdDistrib P.NormalizedPair Q.NormalizedPair (Fin 2)).trans
      (Equiv.sumCongr P.pairEndpointEquiv Q.pairEndpointEquiv)
  refine (Pairing.ofSplit e P Q).normalizedPairEquivOfEndpointEquiv endpointEquiv e ?_
  intro pr
  cases pr with
  | inl x =>
      change (Pairing.ofSplit e P Q).partner
          (e (Sum.inl (P.pairEndpointEquiv (x, 0)))) =
        e (Sum.inl (P.pairEndpointEquiv (x, 1)))
      rw [Pairing.ofSplit_partner_inl]
      simp only [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint_zero,
        Pairing.pairEndpoint_one]
      exact congrArg (fun j => e (Sum.inl j))
        ((P.mem_pairs_iff x.1.1 x.1.2).mp x.2).2
  | inr x =>
      change (Pairing.ofSplit e P Q).partner
          (e (Sum.inr (Q.pairEndpointEquiv (x, 0)))) =
        e (Sum.inr (Q.pairEndpointEquiv (x, 1)))
      rw [Pairing.ofSplit_partner_inr]
      simp only [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint_zero,
        Pairing.pairEndpoint_one]
      exact congrArg (fun j => e (Sum.inr j))
        ((Q.mem_pairs_iff x.1.1 x.1.2).mp x.2).2
/-- A normalized pair in an arbitrary binary position split has the two transported
endpoints in either their original order or the reverse order. In particular, neither
orientation is silently assumed for fermionic kernels. -/
theorem Pairing.ofSplitNormalizedPairEquiv_pair_eq_or_swap
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (pr : P.NormalizedPair ⊕ Q.NormalizedPair) :
    (Pairing.ofSplitNormalizedPairEquiv e P Q pr).1 =
        (match pr with
         | Sum.inl p => (e (Sum.inl p.1.1), e (Sum.inl p.1.2))
         | Sum.inr p => (e (Sum.inr p.1.1), e (Sum.inr p.1.2))) ∨
      (Pairing.ofSplitNormalizedPairEquiv e P Q pr).1 =
        (match pr with
         | Sum.inl p => (e (Sum.inl p.1.2), e (Sum.inl p.1.1))
         | Sum.inr p => (e (Sum.inr p.1.2), e (Sum.inr p.1.1))) := by
  classical
  let endpointEquiv :
      (P.NormalizedPair ⊕ Q.NormalizedPair) × Fin 2 ≃
        Fin (2 * a) ⊕ Fin (2 * b) :=
    (Equiv.sumProdDistrib P.NormalizedPair Q.NormalizedPair (Fin 2)).trans
      (Equiv.sumCongr P.pairEndpointEquiv Q.pairEndpointEquiv)
  have hpartner (s : P.NormalizedPair ⊕ Q.NormalizedPair) :
      (Pairing.ofSplit e P Q).partner (e (endpointEquiv (s, 0))) =
        e (endpointEquiv (s, 1)) := by
    cases s with
    | inl p =>
        change (Pairing.ofSplit e P Q).partner (e (Sum.inl p.1.1)) =
          e (Sum.inl p.1.2)
        rw [Pairing.ofSplit_partner_inl]
        exact congrArg (fun x => e (Sum.inl x))
          ((P.mem_pairs_iff p.1.1 p.1.2).mp p.2).2
    | inr p =>
        change (Pairing.ofSplit e P Q).partner (e (Sum.inr p.1.1)) =
          e (Sum.inr p.1.2)
        rw [Pairing.ofSplit_partner_inr]
        exact congrArg (fun x => e (Sum.inr x))
          ((Q.mem_pairs_iff p.1.1 p.1.2).mp p.2).2
  change
    ((Pairing.ofSplit e P Q).normalizedPairOfEndpointEquiv endpointEquiv e pr).1 = _ ∨
      ((Pairing.ofSplit e P Q).normalizedPairOfEndpointEquiv endpointEquiv e pr).1 = _
  have h :=
    (Pairing.ofSplit e P Q).normalizedPairOfEndpointEquiv_pair_eq_or_swap
      endpointEquiv e hpartner pr
  cases pr with
  | inl p => simpa [endpointEquiv] using h
  | inr p => simpa [endpointEquiv] using h

/-- A pair from either half of a binary splitting keeps its original endpoint order
whenever the two transported endpoints are already increasing.

Unlike an arbitrary position splitting, this hypothesis rules out an orientation reversal for
the selected pair. In particular, a nonsymmetric fermionic contraction kernel can then be
evaluated on the transported endpoints in their original order. -/
theorem Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (pr : P.NormalizedPair ⊕ Q.NormalizedPair)
    (horder : match pr with
      | Sum.inl p => e (Sum.inl p.1.1) < e (Sum.inl p.1.2)
      | Sum.inr p => e (Sum.inr p.1.1) < e (Sum.inr p.1.2)) :
    (Pairing.ofSplitNormalizedPairEquiv e P Q pr).1 =
      match pr with
      | Sum.inl p => (e (Sum.inl p.1.1), e (Sum.inl p.1.2))
      | Sum.inr p => (e (Sum.inr p.1.1), e (Sum.inr p.1.2)) := by
  rcases Pairing.ofSplitNormalizedPairEquiv_pair_eq_or_swap e P Q pr with h | h
  · cases pr <;> exact h
  · have hnormalized :=
      (Pairing.ofSplit e P Q).pairs_normalized
        (Pairing.ofSplitNormalizedPairEquiv e P Q pr).2
    rw [h] at hnormalized
    cases pr with
    | inl p => exact (lt_asymm horder hnormalized).elim
    | inr p => exact (lt_asymm horder hnormalized).elim

/-- A binary position splitting that is strictly increasing on the left
preserves crossing relations between pairs belonging to that part. -/
theorem Pairing.ofSplitNormalizedPairEquiv_crosses_inl_iff_of_strictMono
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hmono : StrictMono (fun i : Fin (2 * a) => e (Sum.inl i)))
    (p q : P.NormalizedPair) :
    Crosses
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl q)).1 ↔
      Crosses p.1 q.1 := by
  have hp :=
    Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inl p)
      (hmono (P.pairs_normalized p.2))
  have hq :=
    Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inl q)
      (hmono (P.pairs_normalized q.2))
  rw [hp, hq]
  exact crosses_map_iff (fun i => e (Sum.inl i)) hmono
    p.1.1 p.1.2 q.1.1 q.1.2

/-- A binary position splitting that is strictly increasing on the right
preserves crossing relations between pairs belonging to that part. -/
theorem Pairing.ofSplitNormalizedPairEquiv_crosses_inr_iff_of_strictMono
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hmono : StrictMono (fun i : Fin (2 * b) => e (Sum.inr i)))
    (p q : Q.NormalizedPair) :
    Crosses
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1 ↔
      Crosses p.1 q.1 := by
  have hp :=
    Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inr p)
      (hmono (Q.pairs_normalized p.2))
  have hq :=
    Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt e P Q (Sum.inr q)
      (hmono (Q.pairs_normalized q.2))
  rw [hp, hq]
  exact crosses_map_iff (fun i => e (Sum.inr i)) hmono
    p.1.1 p.1.2 q.1.1 q.1.2

/-- The ordered crossing count internal to the left part of an assembled
pairing is its standalone crossing count. Inter-part crossings are excluded. -/
theorem Pairing.ofSplitNormalizedPairEquiv_inl_crossingCount_eq
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hmono : StrictMono (fun i : Fin (2 * a) => e (Sum.inl i))) :
    (∑ p : P.NormalizedPair, ∑ q : P.NormalizedPair,
      if Crosses
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl p)).1
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl q)).1
      then 1 else 0) = P.crossingCount := by
  classical
  rw [P.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact if_congr
    (Pairing.ofSplitNormalizedPairEquiv_crosses_inl_iff_of_strictMono
      e P Q hmono p q) rfl rfl

/-- The ordered crossing count internal to the vacuum/right part of an
assembled pairing is its standalone crossing count. Inter-part crossings remain separate. -/
theorem Pairing.ofSplitNormalizedPairEquiv_inr_crossingCount_eq
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hmono : StrictMono (fun i : Fin (2 * b) => e (Sum.inr i))) :
    (∑ p : Q.NormalizedPair, ∑ q : Q.NormalizedPair,
      if Crosses
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr p)).1
          (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr q)).1
      then 1 else 0) = Q.crossingCount := by
  classical
  rw [Q.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact if_congr
    (Pairing.ofSplitNormalizedPairEquiv_crosses_inr_iff_of_strictMono
      e P Q hmono p q) rfl rfl

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
theorem Pairing.ofSplitInterSectorCrossingCount_mod_two_eq_pairEndpointInversionCount
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
    have hindicator :
        (if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 then 1 else 0) +
          (if Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0) =
        (if Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1 ∨
          Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 then 1 else 0) := by
      by_cases hlt : Crosses (emb (Sum.inl p)).1 (emb (Sum.inr q)).1
      · have hnot : ¬ Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1 :=
          fun h => lt_asymm hlt.1 h.1
        simp [hlt, hnot]
      · by_cases hgt : Crosses (emb (Sum.inr q)).1 (emb (Sum.inl p)).1
        · simp [hlt, hgt]
        · simp [hlt, hgt]
    change _ % 2 = _ % 2
    rw [hindicator]
    simpa using hcross.symm
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

/-- Every crossing in a split pairing lies either within one sector or
between the two sectors. No monotonicity of the splitting is required. -/
theorem Pairing.ofSplit_crossingCount_eq_intrasector_add_inter
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
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

/-- With strictly increasing embeddings of both sectors, the sole extra
crossing count is the explicitly identified inter-sector contribution. -/
theorem Pairing.ofSplit_crossingCount_eq_left_add_right_add_inter
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (hleft : StrictMono (fun i : Fin (2 * a) => e (Sum.inl i)))
    (hright : StrictMono (fun i : Fin (2 * b) => e (Sum.inr i))) :
    (Pairing.ofSplit e P Q).crossingCount =
      P.crossingCount + Q.crossingCount +
        Pairing.ofSplitInterSectorCrossingCount e P Q := by
  rw [Pairing.ofSplit_crossingCount_eq_intrasector_add_inter,
    Pairing.ofSplitNormalizedPairEquiv_inl_crossingCount_eq e P Q hleft,
    Pairing.ofSplitNormalizedPairEquiv_inr_crossingCount_eq e P Q hright]

/-- The contraction product of a pairing reassembled from two independent parts splits into
two local contraction products when the corresponding normalized pair values agree.

The slot splitting need not preserve the linear order of positions. The hypotheses refer to
the *normalized ambient pairs* given by `ofSplitNormalizedPairEquiv`, so that any reversal
of a transported pair is handled by the local kernel comparison rather than silently dropped. -/
theorem Pairing.prod_pairs_ofSplit
    {R : Type*} [CommMonoid R]
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (value : Fin (2 * n) → Fin (2 * n) → R)
    (leftValue : Fin (2 * a) → Fin (2 * a) → R)
    (rightValue : Fin (2 * b) → Fin (2 * b) → R)
    (hleft : ∀ pr : P.NormalizedPair,
      value (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl pr)).1.1
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inl pr)).1.2 =
      leftValue pr.1.1 pr.1.2)
    (hright : ∀ pr : Q.NormalizedPair,
      value (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr pr)).1.1
        (Pairing.ofSplitNormalizedPairEquiv e P Q (Sum.inr pr)).1.2 =
      rightValue pr.1.1 pr.1.2) :
    (∏ pr ∈ (Pairing.ofSplit e P Q).pairs, value pr.1 pr.2) =
      (∏ pr ∈ P.pairs, leftValue pr.1 pr.2) *
      ∏ pr ∈ Q.pairs, rightValue pr.1 pr.2 := by
  classical
  let split := Pairing.ofSplitNormalizedPairEquiv e P Q
  calc
    (∏ pr ∈ (Pairing.ofSplit e P Q).pairs, value pr.1 pr.2) =
        ∏ pr : (Pairing.ofSplit e P Q).NormalizedPair,
          value pr.1.1 pr.1.2 :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ pr : P.NormalizedPair ⊕ Q.NormalizedPair,
          value (split pr).1.1 (split pr).1.2 :=
      (Equiv.prod_comp split (fun pr => value pr.1.1 pr.1.2)).symm
    _ = (∏ pr : P.NormalizedPair,
          value (split (Sum.inl pr)).1.1 (split (Sum.inl pr)).1.2) *
        ∏ pr : Q.NormalizedPair,
          value (split (Sum.inr pr)).1.1 (split (Sum.inr pr)).1.2 :=
      Fintype.prod_sum_type _
    _ = (∏ pr : P.NormalizedPair, leftValue pr.1.1 pr.1.2) *
        ∏ pr : Q.NormalizedPair, rightValue pr.1.1 pr.1.2 := by
      congr 1
      · apply Fintype.prod_congr
        intro pr
        exact hleft pr
      · apply Fintype.prod_congr
        intro pr
        exact hright pr
    _ = _ := by
      rw [← Finset.prod_subtype P.pairs (fun _ => Iff.rfl)
        (fun pr => leftValue pr.1 pr.2),
        ← Finset.prod_subtype Q.pairs (fun _ => Iff.rfl)
        (fun pr => rightValue pr.1 pr.2)]

end Combinatorics
