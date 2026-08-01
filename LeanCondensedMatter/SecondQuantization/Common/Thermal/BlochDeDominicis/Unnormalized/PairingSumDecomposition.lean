import LeanCondensedMatter.Combinatorics.PerfectPairing.SumDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PairingTermFirstPair

set_option linter.style.header false

/-!
# Pairing-sum decomposition by the partner of position `0`

The finite sum over all `Pairing (n + 1)` is reindexed by the partner of `0` and a smaller
`Pairing n`, then each term is rewritten using the first-pair decomposition.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

/-- Decompose the pairing sum into a sum over the chosen partner of position `0` and a smaller
pairing. -/
theorem pairingSum_eq_sum_sum_insertFirstPair {n : ℕ} (β : ℝ) (H : Hamiltonian 𝓢 N)
    (C : Fin (2 * (n + 1)) → OperatorTime 𝓢 N) :
    pairingSum β H (n + 1) C =
      ∑ j : Fin (2 * n + 1), ∑ Q : Pairing n,
        pairingTerm β H (Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))) C := by
  rw [pairingSum, Pairing.sum_eq_sum_sum_insertFirstPair]

end BlochDeDominicis
end Common
end SecondQuantization
