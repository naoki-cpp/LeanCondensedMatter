import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

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



end Combinatorics
