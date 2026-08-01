import LeanCondensedMatter.Combinatorics.PerfectPairing.PairsDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PairingTerm

set_option linter.style.header false

/-!
# `pairingTerm`, decomposed along the pair containing position `0`

This is the algebraic bridge used by the pairing-sum recursion: the product over all pairs splits
into the contraction of the first pair and the product attached to the smaller erased pairing.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

/-- `pairingTerm` decomposes into the first-pair contraction, the smaller pairing term, and the
statistics factor contributed by the first pair's crossings. -/
theorem pairingTerm_eq_firstPair_mul {n : ℕ} (β : ℝ) (H : Hamiltonian 𝓢 N)
    (pairing : Pairing (n + 1)) (C : Fin (2 * (n + 1)) → OperatorTime 𝓢 N) :
    pairingTerm β H pairing C =
      𝓢.exchangeSign ^ pairing.crossingsWithFirstPair *
        thermalContract β H (C 0) (C (pairing.partner 0)) *
        pairingTerm β H pairing.eraseZeroPair
          (fun i => C (pairing.eraseZeroOrderIso i)) := by
  rw [pairingTerm, pairingTerm, pairingWeight, pairingWeight,
    pairing.crossingCount_eraseZeroPair, pow_add, pairing.prod_pairs_eq_firstPair_mul]
  simp only [Pairing.firstPair]
  ring

end BlochDeDominicis
end Common
end SecondQuantization
