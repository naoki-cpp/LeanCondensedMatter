import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

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
