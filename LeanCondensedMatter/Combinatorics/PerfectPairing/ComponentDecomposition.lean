import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

set_option linter.style.header false

/-!
# Component decompositions of perfect pairings

A global perfect pairing may be assembled from component-local pairings when the component position
fibers partition the global positions, preserve each local order, and intertwine partner maps. Under
those hypotheses, the dependent sum of local normalized pairs is equivalent to the normalized pairs
of the global pairing.
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
when the component position fibers partition the ambient positions, preserve local order, and
intertwine partner maps. -/
noncomputable def Pairing.normalizedPairSigmaEquiv [Fintype ι]
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (_hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩)) :
    (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair :=
  global.normalizedPairEquivOfEndpointEquiv
    (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv
    (by
      rintro ⟨B, pr⟩
      have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
      rw [Pairing.componentPairEndpointEquiv_apply_zero,
        Pairing.componentPairEndpointEquiv_apply_one,
        hpartner B pr.1.1, hpr.2])

@[simp]
theorem Pairing.normalizedPairSigmaEquiv_apply [Fintype ι]
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩))
    (B : ι) (pr : (componentPairing B).NormalizedPair) :
    (global.normalizedPairSigmaEquiv componentPairing positionEquiv hpartner hmono ⟨B, pr⟩).1 =
      (positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩) := by
  change
    (global.normalizedPairOfEndpointEquiv
      (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv ⟨B, pr⟩).1 = _
  unfold Pairing.normalizedPairOfEndpointEquiv
  rw [Pairing.componentPairEndpointEquiv_apply_zero]
  have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
  have horder : positionEquiv ⟨B, pr.1.1⟩ < positionEquiv ⟨B, pr.1.2⟩ :=
    hmono B hpr.1
  simp [Pairing.positionToPairEndpoint, hpartner B pr.1.1, hpr.2, horder]

end Combinatorics
