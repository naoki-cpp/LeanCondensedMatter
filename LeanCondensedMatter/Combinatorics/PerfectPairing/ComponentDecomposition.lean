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

variable {ι : Type*} {m : ι → ℕ} {n : ℕ}

private noncomputable def Pairing.componentPairEndpointEquiv
    (componentPairing : ∀ B, Pairing (m B)) :
    (Σ B, (componentPairing B).NormalizedPair) × Fin 2 ≃ Σ B, Fin (2 * m B) :=
  (Equiv.sigmaProdDistrib (fun B => (componentPairing B).NormalizedPair) (Fin 2)).trans
    (Equiv.sigmaCongrRight fun B => (componentPairing B).pairEndpointEquiv)

private theorem Pairing.componentPairEndpointEquiv_partner
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (x : Σ B, (componentPairing B).NormalizedPair) :
    global.partner
        (positionEquiv (Pairing.componentPairEndpointEquiv componentPairing (x, 0))) =
      positionEquiv (Pairing.componentPairEndpointEquiv componentPairing (x, 1)) := by
  rcases x with ⟨B, pr⟩
  have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
  simpa [Pairing.componentPairEndpointEquiv] using
    (hpartner B pr.1.1).trans
      (congrArg (fun p => positionEquiv ⟨B, p⟩) hpr.2)

/-- Component-local normalized pairs are equivalent to the normalized pairs of a global pairing
when the component position fibers partition the ambient positions and intertwine partner maps. -/
noncomputable def Pairing.normalizedPairSigmaEquiv
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩) :
    (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair :=
  global.normalizedPairEquivOfEndpointEquiv
    (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv
    (global.componentPairEndpointEquiv_partner componentPairing positionEquiv hpartner)

/-- If each component position map is strictly monotone, the component-pair equivalence preserves
normalized endpoint order exactly. -/
theorem Pairing.normalizedPairSigmaEquiv_apply_of_strictMono
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩))
    (B : ι) (pr : (componentPairing B).NormalizedPair) :
    (global.normalizedPairSigmaEquiv componentPairing positionEquiv hpartner ⟨B, pr⟩).1 =
      (positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩) := by
  change
    (global.normalizedPairOfEndpointEquiv
      (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv ⟨B, pr⟩).1 = _
  apply global.normalizedPairOfEndpointEquiv_pair_eq_of_lt
    (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv
    (global.componentPairEndpointEquiv_partner componentPairing positionEquiv hpartner)
  exact hmono B (((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).1


/-- A product over the pairs of a global pairing factors over component pairings whenever a
component-pair equivalence identifies the normalized endpoints and the pair kernel is local under
that identification. -/
theorem Pairing.prod_pairs_eq_prod_components [Fintype ι]
    {R : Type*} [CommMonoid R] (global : Pairing n)
    (componentPairing : ∀ B, Pairing (m B))
    (componentPairEquiv : (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R)
    (localPairValue : ∀ B, Fin (2 * m B) → Fin (2 * m B) → R)
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
      exact (Finset.prod_subtype
        (componentPairing B).pairs (fun _ => Iff.rfl)
        (fun pr => localPairValue B pr.1 pr.2)).symm

/-- Scalar pairing evaluation factors into a residual factor and component evaluations when both
its weight and its pair kernel respect the component-pair decomposition. -/
theorem Pairing.evaluation_eq_mul_prod_components [Fintype ι]
    {R : Type*} [CommMonoid R] (global : Pairing n)
    (componentPairing : ∀ B, Pairing (m B))
    (componentPairEquiv : (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair)
    (weight factor : R) (localWeight : ι → R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R)
    (localPairValue : ∀ B, Fin (2 * m B) → Fin (2 * m B) → R)
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
