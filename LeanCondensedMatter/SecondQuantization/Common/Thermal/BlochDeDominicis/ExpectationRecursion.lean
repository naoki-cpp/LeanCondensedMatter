import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion

set_option linter.style.header false

/-!
# Expectation first-pair recursion for Bloch–de Dominicis

This module records the smallest contract needed by the arbitrary-length pairing induction.  It is
independent of occupation bases, finite configuration spaces, trace formulas, and density-operator
implementations.

An implementation supplies:

- an expectation of an ordered operator list;
- a two-operator contraction value;
- an admissibility predicate stable under deleting a paired operator;
- normalization of the empty product;
- the first-pair recurrence obtained from its KMS and exchange relations.

Once these data are available, the pairing expansion is purely combinatorial.  A future bosonic
implementation can therefore discharge the same contract with summability-aware KMS proofs, without
introducing a false `Fintype` assumption on bosonic occupation states.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

/-- The minimal normalized expectation/KMS contract used by the Bloch–de Dominicis induction. -/
structure ExpectationPairingRecursion (Operator : Type*) (s : Statistics) where
  /-- Expectation of an ordered list of operators. -/
  expectation : List Operator → ℂ
  /-- The normalized two-operator value used for each pair. -/
  pairValue : Operator → Operator → ℂ
  /-- Families for which the exchange and KMS hypotheses needed by the recurrence hold. -/
  admissible : (n : ℕ) → (Fin (2 * n) → Operator) → Prop
  /-- The empty operator product has expectation one. -/
  expectation_nil : expectation [] = 1
  /-- Admissibility is preserved after removing the first operator and its chosen partner. -/
  admissible_erase : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → Operator), admissible (n + 1) C →
    ∀ j : Fin (2 * n + 1),
      admissible n (fun i : Fin (2 * n) => C ((j.succAbove i).succ))
  /-- The KMS/exchange first-pair recurrence. -/
  expectation_succ : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → Operator), admissible (n + 1) C →
    expectation (List.ofFn C) =
      ∑ j : Fin (2 * n + 1), (s.zetaInt : ℂ) ^ (j : ℕ) *
        pairValue (C 0) (C j.succ) *
        expectation (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))

namespace ExpectationPairingRecursion

variable {Operator : Type*} {s : Statistics}

/-- Any normalized expectation satisfying the first-pair recurrence equals the weighted pairing
sum on every admissible even operator family. -/
theorem expectation_eq_sum_pairing (data : ExpectationPairingRecursion Operator s) :
    ∀ (n : ℕ) (C : Fin (2 * n) → Operator), data.admissible n C →
      data.expectation (List.ofFn C) =
        ∑ pairing : Pairing n,
          pairing.weight s *
            ∏ pr ∈ pairing.pairs, data.pairValue (C pr.1) (C pr.2) := by
  intro n C hC
  have hζ : (s.zetaInt : ℂ) * (s.zetaInt : ℂ) = 1 := by
    have h := zetaInt_pow_eq_of_mod_two_eq s (a := 2) (b := 0) (by omega)
    simpa [pow_two] using h
  have h := moment_eq_pairing_sum_of_first_pair_recursion
    (s.zetaInt : ℂ) hζ
    (fun n C => data.expectation (List.ofFn C))
    data.pairValue data.admissible
    (fun C => by simpa only [List.ofFn_zero] using data.expectation_nil)
    data.admissible_erase data.expectation_succ n C hC
  simpa only [Pairing.weight] using h

end ExpectationPairingRecursion

end BlochDeDominicis
end Common
end SecondQuantization
