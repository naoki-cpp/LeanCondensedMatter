import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import Mathlib.Logic.Equiv.Prod

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
abbrev PairingOn.NormalizedPairSubtype {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) (p : α → Prop) :=
  {pr : pairing.NormalizedPair // p pr.1.1}

/-- The two endpoints of normalized pairs selected by a partner-invariant predicate are equivalent
to the selected ambient positions. -/
noncomputable def PairingOn.normalizedPairSubtypeEndpointEquiv {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) (p : α → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    pairing.NormalizedPairSubtype p × Fin 2 ≃ {i : α // p i} :=
  Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
    (pairing.pairEndpointEquiv.subtypeEquiv (fun x => by
      rcases x with ⟨pr, k⟩
      fin_cases k
      · rfl
      · have hp := ((pairing.mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).2
        change p pr.1.1 ↔ p pr.1.2
        rw [← hp]
        exact hpartner pr.1.1))

@[simp]
theorem PairingOn.normalizedPairSubtypeEndpointEquiv_apply_val {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) (p : α → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (pr : pairing.NormalizedPairSubtype p) (k : Fin 2) :
    (pairing.normalizedPairSubtypeEndpointEquiv p hpartner (pr, k)).1 =
      pairEndpointAt pr.1.1 k := by
  rfl

/-- Reindex normalized pairs selected by a partner-invariant predicate into any local pairing whose
partner is intertwined by the chosen position equivalence. -/
noncomputable def PairingOn.normalizedPairSubtypeEquivOfEndpointEquiv {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (pairing : PairingOn α) (p : α → Prop)
    (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β)
    (localPairing : PairingOn β)
    (hlocal : ∀ pos,
      localPairing.partner (e pos) = e ((pairing.restrict p hpartner).partner pos)) :
    pairing.NormalizedPairSubtype p ≃ localPairing.NormalizedPair := by
  classical
  exact localPairing.normalizedPairEquivOfEndpointEquiv
    (pairing.normalizedPairSubtypeEndpointEquiv p hpartner) e
    (fun pr => by
      rw [hlocal]
      apply congrArg e
      apply Subtype.ext
      rw [pairing.restrict_partner_val]
      exact ((pairing.mem_pairs_iff pr.1.1.1 pr.1.1.2).1 pr.1.2).2)

/-- Transport partner-invariant normalized-pair subsets along a partner-preserving position
equivalence when the selection predicates agree under that equivalence. -/
noncomputable def PairingOn.normalizedPairSubtypeEquivOfPartnerEquiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (source : PairingOn α) (target : PairingOn β) (e : α ≃ β)
    (hpartner : ∀ i, target.partner (e i) = e (source.partner i))
    (p : α → Prop) (q : β → Prop)
    (hstable : ∀ i, p (source.partner i) ↔ p i)
    (hcompat : ∀ i, q (e i) ↔ p i) :
    source.NormalizedPairSubtype p ≃ target.NormalizedPairSubtype q :=
  (source.normalizedPairEquivOfPartnerEquiv target e hpartner).subtypeEquiv
    (fun pr => by
      have hends := target.normalizedPairOfEndpointEquiv_pair_eq_or_swap
        source.pairEndpointEquiv e
        (fun r => by
          change target.partner (e r.1.1) = e r.1.2
          rw [hpartner]
          exact congrArg e (((source.mem_pairs_iff r.1.1 r.1.2).1 r.2).2))
        pr
      change (source.normalizedPairEquivOfPartnerEquiv target e hpartner pr).1 =
          (e pr.1.1, e pr.1.2) ∨
        (source.normalizedPairEquivOfPartnerEquiv target e hpartner pr).1 =
          (e pr.1.2, e pr.1.1) at hends
      rcases hends with h | h
      · rw [congrArg Prod.fst h, hcompat]
      · have hp := ((source.mem_pairs_iff pr.1.1 pr.1.2).mp pr.2).2
        rw [congrArg Prod.fst h, hcompat, ← hp, hstable])

end Combinatorics
