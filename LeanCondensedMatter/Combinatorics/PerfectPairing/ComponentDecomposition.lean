import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct

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
noncomputable def Pairing.normalizedPairSigmaEquiv [Fintype ι]
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
theorem Pairing.normalizedPairSigmaEquiv_apply_of_strictMono [Fintype ι]
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
    (∏ pr ∈ global.pairs, pairValue pr.1 pr.2) =
        ∏ pr : global.NormalizedPair, pairValue pr.1.1 pr.1.2 :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ B, ∏ pr : (componentPairing B).NormalizedPair,
          pairValue (componentPairEquiv ⟨B, pr⟩).1.1
            (componentPairEquiv ⟨B, pr⟩).1.2 := by
      simpa using
        (Fintype.prod_equiv_sigma componentPairEquiv.symm
          (fun pr => pairValue pr.1.1 pr.1.2))
    _ = ∏ B, ∏ pr : (componentPairing B).NormalizedPair,
          localPairValue B pr.1.1 pr.1.2 := by
      simp only [hvalue]
    _ = ∏ B, ∏ pr ∈ (componentPairing B).pairs,
          localPairValue B pr.1 pr.2 := by
      apply Fintype.prod_congr
      intro B
      exact (Finset.prod_subtype
        (componentPairing B).pairs (fun _ => Iff.rfl)
        (fun pr => localPairValue B pr.1 pr.2)).symm

/-- The oriented pairing evaluation is invariant under a
**strictly order-preserving**, partner-intertwining equivalence of
the actual finite positions, provided the endpoint kernel is pulled
back along that same equivalence. Both endpoints of a normalized
fermion contraction retain their orientation; no symmetry assumption
on the kernel is required. -/
theorem Pairing.evaluation_eq_of_partnerEquiv_strictMono
    {a b : ℕ} {R : Type*} [CommMonoid R]
    (source : Pairing a) (target : Pairing b)
    (e : Fin (2 * a) ≃ Fin (2 * b))
    (hpartner : ∀ p, target.partner (e p) = e (source.partner p))
    (hmono : StrictMono e)
    (weight : R)
    (sourceValue : Fin (2 * a) → Fin (2 * a) → R)
    (targetValue : Fin (2 * b) → Fin (2 * b) → R)
    (hvalue : ∀ i j, sourceValue i j = targetValue (e i) (e j)) :
    source.evaluation weight sourceValue =
      target.evaluation weight targetValue := by
  classical
  let pairEquiv := source.normalizedPairEquivOfPartnerEquiv target e hpartner
  have hpair (pr : source.NormalizedPair) :
      (pairEquiv pr).1 = (e pr.1.1, e pr.1.2) :=
    source.normalizedPairEquivOfPartnerEquiv_apply_of_strictMono
      target e hpartner hmono pr
  unfold Pairing.evaluation
  apply congrArg (fun z : R => weight * z)
  calc
    (∏ pr ∈ source.pairs, sourceValue pr.1 pr.2) =
        ∏ pr : source.NormalizedPair, sourceValue pr.1.1 pr.1.2 :=
      Finset.prod_subtype source.pairs (fun _ => Iff.rfl) _
    _ = ∏ pr : source.NormalizedPair,
          targetValue (pairEquiv pr).1.1 (pairEquiv pr).1.2 := by
      apply Finset.prod_congr rfl
      intro pr _
      rw [hpair pr]
      exact hvalue pr.1.1 pr.1.2
    _ = ∏ pr : target.NormalizedPair, targetValue pr.1.1 pr.1.2 :=
      Equiv.prod_comp pairEquiv
        (fun pr : target.NormalizedPair => targetValue pr.1.1 pr.1.2)
    _ = ∏ pr ∈ target.pairs, targetValue pr.1 pr.2 :=
      (Finset.prod_subtype target.pairs (fun _ => Iff.rfl)
        (fun pr => targetValue pr.1 pr.2)).symm

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
  simp only [Pairing.evaluation, Finset.prod_mul_distrib]
  rw [hweight, global.prod_pairs_eq_prod_components componentPairing componentPairEquiv
    pairValue localPairValue hvalue, mul_assoc]

end Combinatorics
