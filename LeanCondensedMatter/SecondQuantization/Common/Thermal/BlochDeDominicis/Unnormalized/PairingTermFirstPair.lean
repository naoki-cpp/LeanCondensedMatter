import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PairingTermDecomposition

set_option linter.style.header false

/-!
# First-pair form of one perfect-pairing contribution

The statistics weight contributed by crossing the first pair is rewritten as the exchange sign to
the number of intervening positions.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

/-- Rewrite one pairing contribution using the position of the partner of `0`. -/
theorem pairingTerm_eq_firstPair_intervening {n : ℕ} (β : ℝ) (H : Hamiltonian 𝓢 N)
    (pairing : Pairing (n + 1)) (C : Fin (2 * (n + 1)) → OperatorTime 𝓢 N) :
    pairingTerm β H pairing C =
      𝓢.exchangeSign ^ pairing.interveningPositionCount *
        thermalContract β H (C 0) (C (pairing.partner 0)) *
        pairingTerm β H pairing.eraseZeroPair
          (fun i => C (pairing.eraseZeroOrderIso i)) := by
  rw [pairingTerm_eq_firstPair_mul]
  congr 1
  exact Combinatorics.pow_eq_of_mod_two_eq FieldStatistic.exchangeSign_mul_self
    pairing.crossingsWithFirstPair_mod_two

end BlochDeDominicis
end Common
end SecondQuantization
