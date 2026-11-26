import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Normalized pairs under a binary position splitting

The normalized endpoint equivalence and product factorization apply to arbitrary position
splittings, including those that reverse a transported pair. Crossing counts and parity belong
to `PerfectPairing.SplitCrossing`; the endpoint and product laws do not import crossing geometry.
-/

namespace Combinatorics

variable {α β γ : Type*}
  [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [Fintype γ] [LinearOrder γ]

/-- Endpoint equivalence for the two local pair families of a binary splitting. -/
private noncomputable def PairingOn.splitPairEndpointEquiv (P : PairingOn α) (Q : PairingOn β) :
    (P.NormalizedPair ⊕ Q.NormalizedPair) × Fin 2 ≃
      α ⊕ β :=
  (Equiv.sumProdDistrib P.NormalizedPair Q.NormalizedPair (Fin 2)).trans
    (Equiv.sumCongr P.pairEndpointEquiv Q.pairEndpointEquiv)

omit [Fintype γ] [LinearOrder γ] in
/-- Partner compatibility of the transported endpoints for a binary pairing split. -/
private theorem PairingOn.ofSplit_pairEndpointEquiv_partner
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (pr : P.NormalizedPair ⊕ Q.NormalizedPair) :
    (PairingOn.ofSplit e P Q).partner
        (e (PairingOn.splitPairEndpointEquiv P Q (pr, 0))) =
      e (PairingOn.splitPairEndpointEquiv P Q (pr, 1)) := by
  cases pr with
  | inl p =>
      change (PairingOn.ofSplit e P Q).partner (e (Sum.inl p.1.1)) =
        e (Sum.inl p.1.2)
      rw [PairingOn.ofSplit_partner_inl]
      exact congrArg (fun x => e (Sum.inl x))
        ((P.mem_pairs_iff p.1.1 p.1.2).mp p.2).2
  | inr p =>
      change (PairingOn.ofSplit e P Q).partner (e (Sum.inr p.1.1)) =
        e (Sum.inr p.1.2)
      rw [PairingOn.ofSplit_partner_inr]
      exact congrArg (fun x => e (Sum.inr x))
        ((Q.mem_pairs_iff p.1.1 p.1.2).mp p.2).2

/-- Normalized pairs of a pairing assembled from two independent parts are precisely
the normalized pairs of those parts, tagged by their side.

The position splitting is not required to preserve the ambient order: normalization may
reverse an individual transported pair. This equivalence is the reindexing input for
factorizing products of pair contractions over an arbitrary slot shuffle. -/
noncomputable def PairingOn.ofSplitNormalizedPairEquiv
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    P.NormalizedPair ⊕ Q.NormalizedPair ≃ (PairingOn.ofSplit e P Q).NormalizedPair :=
  (PairingOn.ofSplit e P Q).normalizedPairEquivOfEndpointEquiv
    (PairingOn.splitPairEndpointEquiv P Q) e
    (PairingOn.ofSplit_pairEndpointEquiv_partner e P Q)

/-- A normalized pair in an arbitrary binary position split has the two transported
endpoints in either their original order or the reverse order. In particular, neither
orientation is silently assumed for fermionic kernels. -/
theorem PairingOn.ofSplitNormalizedPairEquiv_pair_eq_or_swap
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (pr : P.NormalizedPair ⊕ Q.NormalizedPair) :
    (PairingOn.ofSplitNormalizedPairEquiv e P Q pr).1 =
        (match pr with
         | Sum.inl p => (e (Sum.inl p.1.1), e (Sum.inl p.1.2))
         | Sum.inr p => (e (Sum.inr p.1.1), e (Sum.inr p.1.2))) ∨
      (PairingOn.ofSplitNormalizedPairEquiv e P Q pr).1 =
        (match pr with
         | Sum.inl p => (e (Sum.inl p.1.2), e (Sum.inl p.1.1))
         | Sum.inr p => (e (Sum.inr p.1.2), e (Sum.inr p.1.1))) := by
  change
    ((PairingOn.ofSplit e P Q).normalizedPairOfEndpointEquiv
      (PairingOn.splitPairEndpointEquiv P Q) e pr).1 = _ ∨
      ((PairingOn.ofSplit e P Q).normalizedPairOfEndpointEquiv
        (PairingOn.splitPairEndpointEquiv P Q) e pr).1 = _
  have h :=
    (PairingOn.ofSplit e P Q).normalizedPairOfEndpointEquiv_pair_eq_or_swap
      (PairingOn.splitPairEndpointEquiv P Q) e
      (PairingOn.ofSplit_pairEndpointEquiv_partner e P Q) pr
  cases pr with
  | inl p => simpa [PairingOn.splitPairEndpointEquiv] using h
  | inr p => simpa [PairingOn.splitPairEndpointEquiv] using h

/-- A pair from either half of a binary splitting keeps its original endpoint order
whenever the two transported endpoints are already increasing.

Unlike an arbitrary position splitting, this hypothesis rules out an orientation reversal for
the selected pair. In particular, a nonsymmetric fermionic contraction kernel can then be
evaluated on the transported endpoints in their original order. -/
theorem PairingOn.ofSplitNormalizedPairEquiv_pair_eq_of_lt
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (pr : P.NormalizedPair ⊕ Q.NormalizedPair)
    (horder : match pr with
      | Sum.inl p => e (Sum.inl p.1.1) < e (Sum.inl p.1.2)
      | Sum.inr p => e (Sum.inr p.1.1) < e (Sum.inr p.1.2)) :
    (PairingOn.ofSplitNormalizedPairEquiv e P Q pr).1 =
      match pr with
      | Sum.inl p => (e (Sum.inl p.1.1), e (Sum.inl p.1.2))
      | Sum.inr p => (e (Sum.inr p.1.1), e (Sum.inr p.1.2)) := by
  have h :=
    (PairingOn.ofSplit e P Q).normalizedPairOfEndpointEquiv_pair_eq_of_lt
      (PairingOn.splitPairEndpointEquiv P Q) e
      (PairingOn.ofSplit_pairEndpointEquiv_partner e P Q) pr (by
        cases pr with
        | inl p => exact horder
        | inr p => exact horder)
  change
    ((PairingOn.ofSplit e P Q).normalizedPairOfEndpointEquiv
      (PairingOn.splitPairEndpointEquiv P Q) e pr).1 = _
  cases pr with
  | inl p => simpa [PairingOn.splitPairEndpointEquiv] using h
  | inr p => simpa [PairingOn.splitPairEndpointEquiv] using h

/-- The contraction product of a pairing reassembled from two independent parts splits into
two local contraction products when the corresponding normalized pair values agree.

The slot splitting need not preserve the linear order of positions. The hypotheses refer to
the *normalized ambient pairs* given by `ofSplitNormalizedPairEquiv`, so that any reversal
of a transported pair is handled by the local kernel comparison rather than silently dropped. -/
theorem PairingOn.prod_pairs_ofSplit
    {R : Type*} [CommMonoid R]
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (value : γ → γ → R)
    (leftValue : α → α → R)
    (rightValue : β → β → R)
    (hleft : ∀ pr : P.NormalizedPair,
      value (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl pr)).1.1
        (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inl pr)).1.2 =
      leftValue pr.1.1 pr.1.2)
    (hright : ∀ pr : Q.NormalizedPair,
      value (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr pr)).1.1
        (PairingOn.ofSplitNormalizedPairEquiv e P Q (Sum.inr pr)).1.2 =
      rightValue pr.1.1 pr.1.2) :
    (∏ pr ∈ (PairingOn.ofSplit e P Q).pairs, value pr.1 pr.2) =
      (∏ pr ∈ P.pairs, leftValue pr.1 pr.2) *
      ∏ pr ∈ Q.pairs, rightValue pr.1 pr.2 := by
  classical
  calc
    _ = ∏ pr : P.NormalizedPair ⊕ Q.NormalizedPair,
        Sum.elim (fun p => leftValue p.1.1 p.1.2)
          (fun q => rightValue q.1.1 q.1.2) pr := by
      apply (PairingOn.ofSplit e P Q).prod_pairs_eq_prod_of_equiv
        (PairingOn.ofSplitNormalizedPairEquiv e P Q) value
      intro pr
      cases pr with
      | inl p => exact hleft p
      | inr q => exact hright q
    _ = _ := by
      rw [Fintype.prod_sum_type]
      exact congrArg₂ (· * ·)
        (P.prod_normalizedPair_eq_prod_pairs leftValue)
        (Q.prod_normalizedPair_eq_prod_pairs rightValue)

end Combinatorics
