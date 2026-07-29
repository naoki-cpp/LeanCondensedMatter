import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Endpoints of normalized pairs

Every position of a perfect pairing occurs exactly once among the two endpoints of its normalized
pairs.  This file packages that fact as an explicit equivalence, used to reindex sums over
pair-of-pair endpoint comparisons as sums over the ambient paired positions.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- A normalized pair belonging to a fixed pairing. -/
abbrev Pairing.NormalizedPair {n : ℕ} (pairing : Pairing n) :=
  {pair : Fin (2 * n) × Fin (2 * n) // pair ∈ pairing.pairs}

/-- Select endpoint `0` or endpoint `1` of a normalized pair. -/
def Pairing.pairEndpoint {n : ℕ} (pairing : Pairing n) :
    pairing.NormalizedPair × Fin 2 → Fin (2 * n) :=
  fun x => if x.2 = 0 then x.1.1.1 else x.1.1.2

/-- Recover the normalized pair and endpoint index containing a position. -/
noncomputable def Pairing.positionToPairEndpoint {n : ℕ} (pairing : Pairing n) :
    Fin (2 * n) → pairing.NormalizedPair × Fin 2 := by
  classical
  intro i
  by_cases h : i < pairing.partner i
  · exact (⟨(i, pairing.partner i), (pairing.mem_pairs_iff i (pairing.partner i)).2 ⟨h, rfl⟩⟩, 0)
  · exact (⟨(pairing.partner i, i), (pairing.mem_pairs_iff (pairing.partner i) i).2
      ⟨lt_of_le_of_ne (le_of_not_gt h) (pairing.partner_ne i), pairing.partner_partner i⟩⟩, 1)

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
    · simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, hablt, hpartnera]
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hablt)
      simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, hba, hpartnerb]
  right_inv := by
    intro i
    by_cases h : i < pairing.partner i
    · simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, h]
    · simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, h]

@[simp]
theorem Pairing.pairEndpointEquiv_apply {n : ℕ} (pairing : Pairing n)
    (x : pairing.NormalizedPair × Fin 2) :
    pairing.pairEndpointEquiv x = pairing.pairEndpoint x :=
  rfl

end BlochDeDominicis
end Common
end SecondQuantization
