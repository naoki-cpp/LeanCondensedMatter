import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PairingTerm

set_option linter.style.header false

/-!
# Finite sum over perfect pairings

The unnormalized Bloch--de Dominicis right-hand side is the sum of `pairingTerm` over all perfect
pairings.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

/-- The finite sum of all perfect-pairing contributions. -/
noncomputable def pairingSum (β : ℝ) (H : Hamiltonian 𝓢 N)
    (n : ℕ) (C : Fin (2 * n) → OperatorTime 𝓢 N) : ℂ :=
  ∑ pairing : Pairing n, pairingTerm β H pairing C

end BlochDeDominicis
end Common
end SecondQuantization
