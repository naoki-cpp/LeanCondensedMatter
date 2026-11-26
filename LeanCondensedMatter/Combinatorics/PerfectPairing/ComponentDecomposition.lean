import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Component decompositions of perfect pairings

A global perfect pairing may be assembled from component-local pairings when the component position
fibers partition the global positions and intertwine partner maps. Under those hypotheses, the
dependent sum of local normalized pairs is equivalent to the normalized pairs of the global pairing.
A local-order hypothesis is needed only when identifying transported normalized endpoints without a
swap. Scalar evaluation factors over the same decomposition when its global weight is a residual
factor times the product of local weights.
-/

namespace Combinatorics

variable {ι α : Type*} {β : ι → Type*}
  [Fintype α] [LinearOrder α] [∀ B, Fintype (β B)] [∀ B, LinearOrder (β B)]

private noncomputable def PairingOn.componentPairEndpointEquiv
    (componentPairing : ∀ B, PairingOn (β B)) :
    (Σ B, (componentPairing B).NormalizedPair) × Fin 2 ≃ Σ B, β B :=
  (Equiv.sigmaProdDistrib (fun B => (componentPairing B).NormalizedPair) (Fin 2)).trans
    (Equiv.sigmaCongrRight fun B => (componentPairing B).pairEndpointEquiv)

omit [Fintype α] [LinearOrder α] in
private theorem PairingOn.componentPairEndpointEquiv_partner
    (global : PairingOn α) (componentPairing : ∀ B, PairingOn (β B))
    (positionEquiv : (Σ B, β B) ≃ α)
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (x : Σ B, (componentPairing B).NormalizedPair) :
    global.partner
        (positionEquiv (PairingOn.componentPairEndpointEquiv componentPairing (x, 0))) =
      positionEquiv (PairingOn.componentPairEndpointEquiv componentPairing (x, 1)) := by
  rcases x with ⟨B, pr⟩
  have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
  simpa [PairingOn.componentPairEndpointEquiv] using
    (hpartner B pr.1.1).trans
      (congrArg (fun p => positionEquiv ⟨B, p⟩) hpr.2)

/-- Component-local normalized pairs are equivalent to the normalized pairs of a global pairing
when the component position fibers partition the ambient positions and intertwine partner maps. -/
noncomputable def PairingOn.normalizedPairSigmaEquiv
    (global : PairingOn α) (componentPairing : ∀ B, PairingOn (β B))
    (positionEquiv : (Σ B, β B) ≃ α)
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩) :
    (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair :=
  global.normalizedPairEquivOfEndpointEquiv
    (PairingOn.componentPairEndpointEquiv componentPairing) positionEquiv
    (global.componentPairEndpointEquiv_partner componentPairing positionEquiv hpartner)

/-- If each component position map is strictly monotone, the component-pair equivalence preserves
normalized endpoint order exactly. -/
theorem PairingOn.normalizedPairSigmaEquiv_apply_of_strictMono
    (global : PairingOn α) (componentPairing : ∀ B, PairingOn (β B))
    (positionEquiv : (Σ B, β B) ≃ α)
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩))
    (B : ι) (pr : (componentPairing B).NormalizedPair) :
    (global.normalizedPairSigmaEquiv componentPairing positionEquiv hpartner ⟨B, pr⟩).1 =
      (positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩) := by
  change
    (global.normalizedPairOfEndpointEquiv
      (PairingOn.componentPairEndpointEquiv componentPairing) positionEquiv ⟨B, pr⟩).1 = _
  apply global.normalizedPairOfEndpointEquiv_pair_eq_of_lt
    (PairingOn.componentPairEndpointEquiv componentPairing) positionEquiv
    (global.componentPairEndpointEquiv_partner componentPairing positionEquiv hpartner)
  exact hmono B (((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).1


/-- A product over the pairs of a global pairing factors over component pairings whenever a
component-pair equivalence identifies the normalized endpoints and the pair kernel is local under
that identification. -/
theorem PairingOn.prod_pairs_eq_prod_components [Fintype ι]
    {R : Type*} [CommMonoid R] (global : PairingOn α)
    (componentPairing : ∀ B, PairingOn (β B))
    (componentPairEquiv : (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair)
    (pairValue : α → α → R)
    (localPairValue : ∀ B, β B → β B → R)
    (hvalue : ∀ B pr,
      pairValue (componentPairEquiv ⟨B, pr⟩).1.1
          (componentPairEquiv ⟨B, pr⟩).1.2 =
        localPairValue B pr.1.1 pr.1.2) :
    (∏ pr ∈ global.pairs, pairValue pr.1 pr.2) =
      ∏ B, ∏ pr ∈ (componentPairing B).pairs,
        localPairValue B pr.1 pr.2 := by
  classical
  calc
    _ = ∏ pr : (Σ B, (componentPairing B).NormalizedPair),
        localPairValue pr.1 pr.2.1.1 pr.2.1.2 :=
      global.prod_pairs_eq_prod_of_equiv componentPairEquiv pairValue _
        (fun pr => hvalue pr.1 pr.2)
    _ = _ := by
      rw [Fintype.prod_sigma]
      apply Fintype.prod_congr
      intro B
      exact (componentPairing B).prod_normalizedPair_eq_prod_pairs (localPairValue B)

/-- Scalar pairing evaluation factors into a residual factor and component evaluations when both
its weight and its pair kernel respect the component-pair decomposition. -/
theorem PairingOn.evaluation_eq_mul_prod_components [Fintype ι]
    {R : Type*} [CommMonoid R] (global : PairingOn α)
    (componentPairing : ∀ B, PairingOn (β B))
    (componentPairEquiv : (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair)
    (weight factor : R) (localWeight : ι → R)
    (pairValue : α → α → R)
    (localPairValue : ∀ B, β B → β B → R)
    (hweight : weight = factor * ∏ B, localWeight B)
    (hvalue : ∀ B pr,
      pairValue (componentPairEquiv ⟨B, pr⟩).1.1
          (componentPairEquiv ⟨B, pr⟩).1.2 =
        localPairValue B pr.1.1 pr.1.2) :
    global.evaluation weight pairValue =
      factor * ∏ B, (componentPairing B).evaluation (localWeight B) (localPairValue B) := by
  classical
  simp only [PairingOn.evaluation, Finset.prod_mul_distrib]
  rw [hweight, global.prod_pairs_eq_prod_components componentPairing componentPairEquiv
    pairValue localPairValue hvalue, mul_assoc]

end Combinatorics
