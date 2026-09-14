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

private noncomputable def Pairing.componentPairMap
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩)) :
    (Σ B, (componentPairing B).NormalizedPair) → global.NormalizedPair :=
  fun x => by
    rcases x with ⟨B, pr⟩
    refine ⟨(positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩), ?_⟩
    have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
    exact (global.mem_pairs_iff _ _).2
      ⟨hmono B hpr.1, by rw [hpartner B pr.1.1, hpr.2]⟩

@[simp]
private theorem Pairing.componentPairMap_apply
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩))
    (B : ι) (pr : (componentPairing B).NormalizedPair) :
    (global.componentPairMap componentPairing positionEquiv hpartner hmono ⟨B, pr⟩).1 =
      (positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩) :=
  rfl

/-- Component-local normalized pairs are equivalent to the normalized pairs of a global pairing
when the component position fibers partition the ambient positions, preserve local order, and
intertwine partner maps. -/
noncomputable def Pairing.normalizedPairSigmaEquiv [Fintype ι]
    (global : Pairing n) (componentPairing : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (componentPairing B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩)) :
    (Σ B, (componentPairing B).NormalizedPair) ≃ global.NormalizedPair :=
  Equiv.ofBijective
    (global.componentPairMap componentPairing positionEquiv hpartner hmono)
    (by
      have hendpoint : ∀ a : Σ B, (componentPairing B).NormalizedPair,
          global.partner
              (positionEquiv (Pairing.componentPairEndpointEquiv componentPairing (a, 0))) =
            positionEquiv (Pairing.componentPairEndpointEquiv componentPairing (a, 1)) := by
        rintro ⟨B, pr⟩
        have hpr := ((componentPairing B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
        rw [Pairing.componentPairEndpointEquiv_apply_zero,
          Pairing.componentPairEndpointEquiv_apply_one,
          hpartner B pr.1.1, hpr.2]
      have hmap :
          global.componentPairMap componentPairing positionEquiv hpartner hmono =
            global.normalizedPairOfEndpointEquiv
              (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv := by
        funext x
        rcases x with ⟨B, pr⟩
        have hrecover := congrArg Prod.fst
          (global.pairEndpointEquiv.left_inv
            (global.componentPairMap componentPairing positionEquiv hpartner hmono ⟨B, pr⟩,
              (0 : Fin 2)))
        have hrecover' :
            (global.positionToPairEndpoint (positionEquiv ⟨B, pr.1.1⟩)).1 =
              global.componentPairMap componentPairing positionEquiv hpartner hmono ⟨B, pr⟩ := by
          simpa only [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint_zero,
            Pairing.componentPairMap_apply] using hrecover
        symm
        unfold Pairing.normalizedPairOfEndpointEquiv
        rw [Pairing.componentPairEndpointEquiv_apply_zero]
        exact hrecover'
      rw [hmap]
      exact (global.normalizedPairEquivOfEndpointEquiv
        (Pairing.componentPairEndpointEquiv componentPairing) positionEquiv hendpoint).bijective)

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
  change (global.componentPairMap componentPairing positionEquiv hpartner hmono ⟨B, pr⟩).1 = _
  rfl

end Combinatorics
