import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Endpoints of normalized pairs

Every position of a perfect pairing occurs exactly once among the two endpoints of its normalized
pairs. This file packages that fact as an explicit equivalence, used to reindex sums over
pair-of-pair endpoint comparisons as sums over the ambient paired positions.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- A normalized pair belonging to a fixed pairing. -/
abbrev Pairing.NormalizedPair {n : ℕ} (pairing : Pairing n) :=
  {pair : Fin (2 * n) × Fin (2 * n) // pair ∈ pairing.pairs}

/-- Select endpoint `0` or endpoint `1` of an ordered pair. -/
def pairEndpointAt {n : ℕ} (pair : Fin (2 * n) × Fin (2 * n)) (k : Fin 2) : Fin (2 * n) :=
  if k = 0 then pair.1 else pair.2

@[simp]
theorem pairEndpointAt_zero {n : ℕ} (pair : Fin (2 * n) × Fin (2 * n)) :
    pairEndpointAt pair 0 = pair.1 := by
  simp [pairEndpointAt]

@[simp]
theorem pairEndpointAt_one {n : ℕ} (pair : Fin (2 * n) × Fin (2 * n)) :
    pairEndpointAt pair 1 = pair.2 := by
  simp [pairEndpointAt]

/-- Select endpoint `0` or endpoint `1` of a normalized pair. -/
def Pairing.pairEndpoint {n : ℕ} (pairing : Pairing n) :
    pairing.NormalizedPair × Fin 2 → Fin (2 * n) :=
  fun x => pairEndpointAt x.1.1 x.2

@[simp]
theorem Pairing.pairEndpoint_eq_pairEndpointAt {n : ℕ}
    (pairing : Pairing n) (p : pairing.NormalizedPair) (k : Fin 2) :
    pairing.pairEndpoint (p, k) = pairEndpointAt p.1 k :=
  rfl

/-- Recover the normalized pair and endpoint index containing a position. -/
noncomputable def Pairing.positionToPairEndpoint {n : ℕ} (pairing : Pairing n) :
    Fin (2 * n) → pairing.NormalizedPair × Fin 2 := by
  classical
  intro i
  by_cases h : i < pairing.partner i
  · exact (⟨(i, pairing.partner i),
      (pairing.mem_pairs_iff i (pairing.partner i)).2 ⟨h, rfl⟩⟩, 0)
  · exact (⟨(pairing.partner i, i),
      (pairing.mem_pairs_iff (pairing.partner i) i).2
        ⟨lt_of_le_of_ne (le_of_not_gt h) (pairing.partner_ne i),
          pairing.partner_partner i⟩⟩, 1)

/-- The two endpoints of all normalized pairs are equivalent to the ambient paired positions. -/
noncomputable def Pairing.pairEndpointEquiv {n : ℕ} (pairing : Pairing n) :
    pairing.NormalizedPair × Fin 2 ≃ Fin (2 * n) where
  toFun := pairing.pairEndpoint
  invFun := pairing.positionToPairEndpoint
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, k⟩
    have hpair := (pairing.mem_pairs_iff a b).1 hab
    have hablt : a < b := hpair.1
    have hpartnera : pairing.partner a = b := hpair.2
    have hpartnerb : pairing.partner b = a := by
      rw [← hpartnera, pairing.partner_partner]
    fin_cases k
    · simp [Pairing.pairEndpoint, pairEndpointAt, Pairing.positionToPairEndpoint, hablt, hpartnera]
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hablt)
      simp [Pairing.pairEndpoint, pairEndpointAt, Pairing.positionToPairEndpoint, hba, hpartnerb]
  right_inv := by
    intro i
    by_cases h : i < pairing.partner i
    · simp [Pairing.pairEndpoint, pairEndpointAt, Pairing.positionToPairEndpoint, h]
    · simp [Pairing.pairEndpoint, pairEndpointAt, Pairing.positionToPairEndpoint, h]

@[simp]
theorem Pairing.pairEndpointEquiv_apply {n : ℕ} (pairing : Pairing n)
    (x : pairing.NormalizedPair × Fin 2) :
    pairing.pairEndpointEquiv x = pairing.pairEndpoint x :=
  rfl

/-- Endpoints selected from distinct normalized pairs are distinct. -/
theorem Pairing.pairEndpoint_ne_of_normalizedPair_ne {n : ℕ} (pairing : Pairing n)
    (p q : pairing.NormalizedPair) (hpq : p ≠ q) (i j : Fin 2) :
    pairing.pairEndpoint (p, i) ≠ pairing.pairEndpoint (q, j) := by
  intro h
  have hargs : (p, i) = (q, j) :=
    pairing.pairEndpointEquiv.injective (by
      simpa only [pairing.pairEndpointEquiv_apply] using h)
  exact hpq (congrArg Prod.fst hargs)

/-- Distinct normalized pairs in one pairing cannot share an endpoint. -/
theorem Pairing.normalizedPair_endpoints_ne_of_ne {n : ℕ} (pairing : Pairing n)
    (p q : pairing.NormalizedPair) (hpq : p ≠ q) :
    p.1.1 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Pairing.pairEndpoint, pairEndpointAt] using
      pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (0 : Fin 2) (0 : Fin 2)
  · simpa [Pairing.pairEndpoint, pairEndpointAt] using
      pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (0 : Fin 2) (1 : Fin 2)
  · simpa [Pairing.pairEndpoint, pairEndpointAt] using
      pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (1 : Fin 2) (0 : Fin 2)
  · simpa [Pairing.pairEndpoint, pairEndpointAt] using
      pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (1 : Fin 2) (1 : Fin 2)

end BlochDeDominicis
end Common
end SecondQuantization
