import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction

set_option linter.style.header false

/-!
# Normalized pairs in partner-invariant position subsets

A partner-invariant predicate on the positions of a perfect pairing also selects whole normalized
pairs. The two endpoints of those selected pairs are canonically equivalent to the selected
positions themselves. This supplies the generic bridge from a restricted ambient pairing to any
reindexed local pairing on the same invariant position subset.
-/

namespace Combinatorics

/-- Normalized pairs whose first endpoint lies in a selected position subset. Partner invariance
ensures that the second endpoint lies in the same subset when needed. -/
abbrev Pairing.NormalizedPairSubtype {n : ℕ} (pairing : Pairing n)
    (p : Fin (2 * n) → Prop) :=
  {pr : pairing.NormalizedPair // p pr.1.1}

/-- The two endpoints of normalized pairs selected by a partner-invariant predicate are equivalent
to the selected ambient positions. -/
noncomputable def Pairing.normalizedPairSubtypeEndpointEquiv {n : ℕ}
    (pairing : Pairing n) (p : Fin (2 * n) → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    pairing.NormalizedPairSubtype p × Fin 2 ≃ {i : Fin (2 * n) // p i} where
  toFun x := by
    rcases x with ⟨pr, k⟩
    refine ⟨pairing.pairEndpoint (pr.1, k), ?_⟩
    fin_cases k
    · simpa using pr.2
    · have hpair := (pairing.mem_pairs_iff pr.1.1.1 pr.1.1.2).1 pr.1.2
      rw [← hpair.2]
      exact (hpartner pr.1.1.1).1 pr.2
  invFun pos := by
    generalize hxdef : pairing.positionToPairEndpoint pos.1 = x
    rcases x with ⟨pr, k⟩
    refine (⟨pr, ?_⟩, k)
    have hx : pairing.pairEndpoint (pr, k) = pos.1 := by
      have h := pairing.pairEndpointEquiv.right_inv pos.1
      change pairing.pairEndpoint (pairing.positionToPairEndpoint pos.1) = pos.1 at h
      rw [hxdef] at h
      exact h
    fin_cases k
    · have hfirst : pr.1.1 = pos.1 := by simpa using hx
      simpa [hfirst] using pos.2
    · have hsecond : pr.1.2 = pos.1 := by simpa using hx
      have hpsecond : p pr.1.2 := by simpa [hsecond] using pos.2
      have hpair := (pairing.mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
      apply (hpartner pr.1.1).2
      rw [hpair.2]
      exact hpsecond
  left_inv x := by
    rcases x with ⟨pr, k⟩
    have h := pairing.pairEndpointEquiv.left_inv (pr.1, k)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change (pairing.positionToPairEndpoint
          (pairing.pairEndpoint (pr.1, k))).2 = k
      exact congrArg Prod.snd h
  right_inv pos := by
    apply Subtype.ext
    exact pairing.pairEndpointEquiv.right_inv pos.1

@[simp]
theorem Pairing.normalizedPairSubtypeEndpointEquiv_apply_zero_val {n : ℕ}
    (pairing : Pairing n) (p : Fin (2 * n) → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (pr : pairing.NormalizedPairSubtype p) :
    (pairing.normalizedPairSubtypeEndpointEquiv p hpartner (pr, 0)).1 = pr.1.1.1 := by
  rfl

@[simp]
theorem Pairing.normalizedPairSubtypeEndpointEquiv_apply_one_val {n : ℕ}
    (pairing : Pairing n) (p : Fin (2 * n) → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (pr : pairing.NormalizedPairSubtype p) :
    (pairing.normalizedPairSubtypeEndpointEquiv p hpartner (pr, 1)).1 = pr.1.1.2 := by
  rfl

/-- On selected normalized-pair endpoints, the restricted partner exchanges endpoint zero and
endpoint one. -/
theorem Pairing.partnerSubtypePerm_normalizedPairSubtypeEndpoint_zero {n : ℕ}
    (pairing : Pairing n) (p : Fin (2 * n) → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (pr : pairing.NormalizedPairSubtype p) :
    pairing.partnerSubtypePerm p hpartner
        (pairing.normalizedPairSubtypeEndpointEquiv p hpartner (pr, 0)) =
      pairing.normalizedPairSubtypeEndpointEquiv p hpartner (pr, 1) := by
  apply Subtype.ext
  rw [pairing.partnerSubtypePerm_val]
  exact ((pairing.mem_pairs_iff pr.1.1.1 pr.1.1.2).1 pr.1.2).2

/-- Reindex normalized pairs selected by a partner-invariant predicate into any local pairing whose
partner is intertwined by the chosen position equivalence. -/
noncomputable def Pairing.normalizedPairSubtypeEquivOfEndpointEquiv {n m : ℕ}
    (pairing : Pairing n) (p : Fin (2 * n) → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : Fin (2 * n) // p i} ≃ Fin (2 * m))
    (localPairing : Pairing m)
    (hlocal : ∀ pos,
      localPairing.partner (e pos) = e (pairing.partnerSubtypePerm p hpartner pos)) :
    pairing.NormalizedPairSubtype p ≃ localPairing.NormalizedPair := by
  classical
  exact localPairing.normalizedPairEquivOfEndpointEquiv
    (pairing.normalizedPairSubtypeEndpointEquiv p hpartner) e
    (fun pr => by
      rw [hlocal, pairing.partnerSubtypePerm_normalizedPairSubtypeEndpoint_zero])

end Combinatorics
