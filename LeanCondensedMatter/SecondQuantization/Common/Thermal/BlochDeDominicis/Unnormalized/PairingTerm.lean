import LeanCondensedMatter.SecondQuantization.Common.Contraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.OperatorTime
import LeanCondensedMatter.SecondQuantization.Common.Thermal.Contraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# The contribution attached to one perfect pairing

Each normalized pair contributes a thermal contraction evaluated at its two endpoints; the full
term is their product multiplied by the statistics-dependent pairing weight.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

/-- The scalar contribution of one perfect pairing. -/
noncomputable def pairingTerm (β : ℝ) (H : Hamiltonian 𝓢 N)
    {n : ℕ} (pairing : Pairing n) (C : Fin (2 * n) → OperatorTime 𝓢 N) : ℂ :=
  pairingWeight 𝓢 pairing *
    ∏ pair ∈ pairing.pairs, thermalContract β H (C pair.1) (C pair.2)

end BlochDeDominicis
end Common
end SecondQuantization
