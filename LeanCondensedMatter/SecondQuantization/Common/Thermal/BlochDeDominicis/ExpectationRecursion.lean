import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion

set_option linter.style.header false

/-!
# Expectation first-pair recursion for Bloch–de Dominicis

This module records the smallest contract needed by the arbitrary-length pairing induction. It is
independent of occupation bases, finite configuration spaces, trace formulas, density-operator
implementations, and the choice of statistical ensemble.

An implementation supplies:

- an expectation of an ordered operator list;
- a two-operator contraction value;
- an admissibility predicate stable under deleting a paired operator;
- normalization of the empty product;
- the first-pair recurrence, often proved from KMS and exchange relations in a concrete state.

Once these data are available, the pairing expansion is purely combinatorial. The contract itself
does not assume a Gibbs state, KMS property, or Gaussianity: a concrete canonical, grand-canonical,
or other state may instantiate it only after proving the stated recurrence. In particular, a
fixed-particle-number Gibbs state is not automatically quasi-free. Bosonic implementations supply
their own summability/domain conditions without imposing `Fintype` on occupation states.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

/-- The minimal normalized expectation/first-pair recurrence contract used by the Bloch–de
Dominicis induction, independent of the statistical ensemble. -/
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
  /-- The first-pair recurrence, to be proved by each concrete state implementation. -/
  expectation_succ : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → Operator), admissible (n + 1) C →
    expectation (List.ofFn C) =
      ∑ j : Fin (2 * n + 1), (s.zetaInt : ℂ) ^ (j : ℕ) *
        pairValue (C 0) (C j.succ) *
        expectation (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))

namespace ExpectationPairingRecursion

variable {Operator : Type*} {s : Statistics}

/-- Any normalized expectation satisfying the first-pair recurrence equals the weighted pairing
sum on every admissible even operator family. -/
theorem bloch_de_dominicis (data : ExpectationPairingRecursion Operator s) :
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
