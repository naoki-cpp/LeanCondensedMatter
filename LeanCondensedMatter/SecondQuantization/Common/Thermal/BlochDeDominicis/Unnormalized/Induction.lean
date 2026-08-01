import LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PairingSum
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.ThermalExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.Admissibility

set_option linter.style.header false

/-!
# Abstract pairing induction for the unnormalized Bloch--de Dominicis theorem

The operator-specific recurrence is discharged before this file. The remaining proof is an
instance of the pure `Combinatorics.moment_eq_pairing_sum_of_first_pair_recursion` theorem.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {𝓢 : FieldStatistic} {N : ℕ}

/-- The unnormalized Bloch--de Dominicis pairing formula for admissible operator-time families. -/
theorem thermalExpectation_eq_pairingSum_of_admissible
    (β : ℝ) (H : Hamiltonian 𝓢 N) :
    ∀ (n : ℕ) (C : Fin (2 * n) → OperatorTime 𝓢 N),
      Admissible n C →
      thermalExpectation β H (List.ofFn C) = pairingSum β H n C := by
  intro n C hC
  unfold pairingSum pairingTerm pairingWeight
  exact moment_eq_pairing_sum_of_first_pair_recursion
    𝓢.exchangeSign FieldStatistic.exchangeSign_mul_self
    (fun n C => thermalExpectation β H (List.ofFn C))
    (fun A B => thermalContract β H A B)
    Admissible
    (fun C => by simp)
    (fun n C hC j => admissible_erase n C hC j)
    (fun n C hC => thermalExpectation_succ β H n C hC)
    n C hC

end BlochDeDominicis
end Common
end SecondQuantization
