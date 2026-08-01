import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PairingSum

set_option linter.style.header false

/-!
# The zero-pairing base case

There is exactly one perfect pairing of `Fin 0`; its pair set is empty and its contribution is one.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

@[simp]
theorem pairingSum_zero (β : ℝ) (H : Hamiltonian 𝓢 N)
    (C : Fin 0 → OperatorTime 𝓢 N) : pairingSum β H 0 C = 1 := by
  have p0 : Pairing 0 :=
    Pairing.ofPartner (Equiv.refl (Fin 0)) ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hUniq : ∀ pairing : Pairing 0, pairing = p0 := fun pairing =>
    Pairing.ext (Equiv.ext fun i => i.elim0)
  have hpairs0 : p0.pairs = (∅ : Finset (Fin 0 × Fin 0)) := by simp [Pairing.pairs]
  have hcc0 : p0.crossingCount = 0 := by simp [Pairing.crossingCount, hpairs0]
  rw [pairingSum, Fintype.sum_eq_single p0 (fun pairing hne => absurd (hUniq pairing) hne)]
  simp [pairingTerm, pairingWeight, hpairs0, hcc0]

end BlochDeDominicis
end Common
end SecondQuantization
