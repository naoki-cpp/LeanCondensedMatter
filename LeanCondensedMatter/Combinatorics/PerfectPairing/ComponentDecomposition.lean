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
    (local : ∀ B, Pairing (m B)) :
    (Σ B, (local B).NormalizedPair) × Fin 2 ≃ Σ B, Fin (2 * m B) :=
  (Equiv.sigmaProdDistrib (fun B => (local B).NormalizedPair) (Fin 2)).trans
    (Equiv.sigmaCongrRight fun B => (local B).pairEndpointEquiv)

@[simp]
private theorem Pairing.componentPairEndpointEquiv_apply_zero
    (local : ∀ B, Pairing (m B)) (B : ι) (pr : (local B).NormalizedPair) :
    Pairing.componentPairEndpointEquiv local (⟨B, pr⟩, 0) = ⟨B, pr.1.1⟩ := by
  simp [Pairing.componentPairEndpointEquiv]

@[simp]
private theorem Pairing.componentPairEndpointEquiv_apply_one
    (local : ∀ B, Pairing (m B)) (B : ι) (pr : (local B).NormalizedPair) :
    Pairing.componentPairEndpointEquiv local (⟨B, pr⟩, 1) = ⟨B, pr.1.2⟩ := by
  simp [Pairing.componentPairEndpointEquiv]

private noncomputable def Pairing.componentPairMap
    (global : Pairing n) (local : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (local B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩)) :
    (Σ B, (local B).NormalizedPair) → global.NormalizedPair :=
  fun x => by
    rcases x with ⟨B, pr⟩
    refine ⟨(positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩), ?_⟩
    have hpr := ((local B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
    exact (global.mem_pairs_iff _ _).2
      ⟨hmono B hpr.1, by rw [hpartner B pr.1.1, hpr.2]⟩

@[simp]
private theorem Pairing.componentPairMap_apply
    (global : Pairing n) (local : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (local B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩))
    (B : ι) (pr : (local B).NormalizedPair) :
    (global.componentPairMap local positionEquiv hpartner hmono ⟨B, pr⟩).1 =
      (positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩) :=
  rfl

/-- Component-local normalized pairs are equivalent to the normalized pairs of a global pairing
when the component position fibers partition the ambient positions, preserve local order, and
intertwine partner maps. -/
noncomputable def Pairing.normalizedPairSigmaEquiv [Fintype ι]
    (global : Pairing n) (local : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (local B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩)) :
    (Σ B, (local B).NormalizedPair) ≃ global.NormalizedPair :=
  Equiv.ofBijective
    (global.componentPairMap local positionEquiv hpartner hmono)
    (by
      have hendpoint : ∀ a : Σ B, (local B).NormalizedPair,
          global.partner
              (positionEquiv (Pairing.componentPairEndpointEquiv local (a, 0))) =
            positionEquiv (Pairing.componentPairEndpointEquiv local (a, 1)) := by
        rintro ⟨B, pr⟩
        have hpr := ((local B).mem_pairs_iff pr.1.1 pr.1.2).1 pr.2
        rw [Pairing.componentPairEndpointEquiv_apply_zero,
          Pairing.componentPairEndpointEquiv_apply_one,
          hpartner B pr.1.1, hpr.2]
      have hmap :
          global.componentPairMap local positionEquiv hpartner hmono =
            global.normalizedPairOfEndpointEquiv
              (Pairing.componentPairEndpointEquiv local) positionEquiv := by
        funext x
        rcases x with ⟨B, pr⟩
        have hrecover := congrArg Prod.fst
          (global.pairEndpointEquiv.left_inv
            (global.componentPairMap local positionEquiv hpartner hmono ⟨B, pr⟩,
              (0 : Fin 2)))
        have hrecover' :
            (global.positionToPairEndpoint (positionEquiv ⟨B, pr.1.1⟩)).1 =
              global.componentPairMap local positionEquiv hpartner hmono ⟨B, pr⟩ := by
          simpa only [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint_zero,
            Pairing.componentPairMap_apply] using hrecover
        symm
        unfold Pairing.normalizedPairOfEndpointEquiv
        rw [Pairing.componentPairEndpointEquiv_apply_zero]
        exact hrecover'
      rw [hmap]
      exact (global.normalizedPairEquivOfEndpointEquiv
        (Pairing.componentPairEndpointEquiv local) positionEquiv hendpoint).bijective)

@[simp]
theorem Pairing.normalizedPairSigmaEquiv_apply [Fintype ι]
    (global : Pairing n) (local : ∀ B, Pairing (m B))
    (positionEquiv : (Σ B, Fin (2 * m B)) ≃ Fin (2 * n))
    (hpartner : ∀ B p,
      global.partner (positionEquiv ⟨B, p⟩) =
        positionEquiv ⟨B, (local B).partner p⟩)
    (hmono : ∀ B, StrictMono (fun p => positionEquiv ⟨B, p⟩))
    (B : ι) (pr : (local B).NormalizedPair) :
    (global.normalizedPairSigmaEquiv local positionEquiv hpartner hmono ⟨B, pr⟩).1 =
      (positionEquiv ⟨B, pr.1.1⟩, positionEquiv ⟨B, pr.1.2⟩) := by
  change (global.componentPairMap local positionEquiv hpartner hmono ⟨B, pr⟩).1 = _
  rfl

end Combinatorics
