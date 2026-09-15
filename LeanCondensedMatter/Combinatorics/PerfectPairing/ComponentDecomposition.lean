import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

set_option linter.style.header false

/-!
# Component decompositions of perfect pairings

A global perfect pairing may be assembled from component-local pairings when the component position
fibers partition the global positions and intertwine partner maps. Under those hypotheses, the
dependent sum of local normalized pairs is equivalent to the normalized pairs of the global pairing.
A local-order hypothesis is needed only when identifying transported normalized endpoints without a
swap.
-/

namespace Combinatorics

variable {ι : Type*} {m : ι → ℕ} {n : ℕ}

private noncomputable def Pairing.componentPairEndpointEquiv
    (componentPairing : ∀ B, Pairing (m B)) :
    (Σ B, (componentPairing B).NormalizedPair) × Fin 2 ≃ Σ B, Fin (2 * m B) :=
  (Equiv.sigmaProdDistrib (fun B => (componentPairing B).NormalizedPair) (Fin 2)).trans
    (Equiv.sigmaCongrRight fun B => (componentPairing B).pairEndpointEquiv)

@[simp]
private theorem Pairing.componentPairEndpointEquiv_apply_zero
    (componentPairing : ∀ B, Pairing (m B))
    (B : ι) (pr : (componentPairing B).NormalizedPair) :
    Pairing.componentPairEndpointEquiv componentPairing (⟨B, pr⟩, 0) = ⟨B, pr.1.1⟩ := by
  simp [Pairing.componentPairEndpointEquiv]

@[simp]
private theorem Pairing.componentPairEndpointEquiv_apply_one
    (componentPairing : ∀ B, Pairing (m B))
    (B : ι) (pr : (componentPairing B).NormalizedPair) :
    Pairing.componentPairEndpointEquiv componentPairing (⟨B, pr⟩, 1) = ⟨B, pr.1.2⟩ := by
  simp [Pairing.componentPairEndpointEquiv]

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
    (by
      rintro ⟨B, pr⟩
      have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
      rw [Pairing.componentPairEndpointEquiv_apply_zero,
        Pairing.componentPairEndpointEquiv_apply_one,
        hpartner B pr.1.1, hpr.2])

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
  apply global.normalizedPairEquivOfEndpointEquiv_pair_eq_of_lt
    (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv
  have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
  exact hmono B hpr.1

end Combinatorics
