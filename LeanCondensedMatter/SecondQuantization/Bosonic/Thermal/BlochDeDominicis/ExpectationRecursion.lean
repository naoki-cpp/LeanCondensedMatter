import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion

set_option linter.style.header false

/-!
# Convergence-aware bosonic expectation pairing recursion

This module is the analytic adapter between a partially defined bosonic Gibbs functional and the
implementation-independent Common Bloch–de Dominicis pairing induction.

The structure below keeps every analytic obligation visible:

- the ordered product must belong to the Gibbs functional's domain on every admissible family;
- admissibility must survive pair deletion;
- the KMS/exchange first-pair recurrence must hold on that domain.

Once those obligations are discharged by a concrete bosonic operator family, the complete pairing
expansion is inherited from Common rather than copied into the bosonic namespace.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

/-- A convergence-aware bosonic implementation of the first-pair recursion contract.

`Observable` is the analytic object evaluated by the Gibbs functional, while `Operator` is the type
of local entries in an ordered product.  They are separated so later matrix-coefficient, quadratic-
form, or completed-operator realizations can share the same adapter. -/
structure ConvergenceAwarePairingRecursion
    (Observable Operator : Type*) [AddCommMonoid Observable] [Module ℂ Observable]
    (s : Common.Statistics) where
  /-- The normalized partial Gibbs functional. -/
  functional : ConvergenceAwareGibbsFunctional Observable
  /-- Ordered multiplication or another justified realization of an operator list. -/
  orderedProduct : List Operator → Observable
  /-- The normalized two-operator contraction value. -/
  pairValue : Operator → Operator → ℂ
  /-- Families satisfying all summability, domain, KMS, and exchange hypotheses. -/
  admissible : (n : ℕ) → (Fin (2 * n) → Operator) → Prop
  /-- Every admissible ordered product lies in the analytic domain of the Gibbs functional. -/
  orderedProduct_mem : ∀ (n : ℕ) (C : Fin (2 * n) → Operator), admissible n C →
    orderedProduct (List.ofFn C) ∈ functional.domain
  /-- The empty ordered product is the functional's distinguished unit. -/
  orderedProduct_nil : orderedProduct [] = functional.unit
  /-- Admissibility, including all analytic obligations, survives deleting a chosen pair. -/
  admissible_erase : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → Operator), admissible (n + 1) C →
    ∀ j : Fin (2 * n + 1),
      admissible n (fun i : Fin (2 * n) => C ((j.succAbove i).succ))
  /-- The convergence-aware KMS/exchange first-pair recurrence. -/
  expectation_succ : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → Operator), admissible (n + 1) C →
    functional.value (orderedProduct (List.ofFn C)) =
      ∑ j : Fin (2 * n + 1), (s.zetaInt : ℂ) ^ (j : ℕ) *
        pairValue (C 0) (C j.succ) *
        functional.value
          (orderedProduct (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ)))

namespace ConvergenceAwarePairingRecursion

variable {Observable Operator : Type*} [AddCommMonoid Observable] [Module ℂ Observable]
  {s : Common.Statistics}

/-- Forget the analytic packaging and expose the total Common first-pair recursion contract.

The total expectation is `ConvergenceAwareGibbsFunctional.value`.  The accompanying
`orderedProduct_mem` field ensures that every admissible family evaluated by the pairing theorem is
inside the genuine analytic domain rather than relying on the zero totalization. -/
noncomputable def toExpectationPairingRecursion
    (data : ConvergenceAwarePairingRecursion Observable Operator s) :
    Common.BlochDeDominicis.ExpectationPairingRecursion Operator s where
  expectation := fun operators => data.functional.value (data.orderedProduct operators)
  pairValue := data.pairValue
  admissible := data.admissible
  expectation_nil := by
    rw [data.orderedProduct_nil]
    exact data.functional.value_unit
  admissible_erase := data.admissible_erase
  expectation_succ := data.expectation_succ

/-- The complete weighted pairing expansion inherited from the Common combinatorial induction. -/
theorem expectation_eq_sum_pairing
    (data : ConvergenceAwarePairingRecursion Observable Operator s)
    (n : ℕ) (C : Fin (2 * n) → Operator) (hC : data.admissible n C) :
    data.functional.value (data.orderedProduct (List.ofFn C)) =
      ∑ pairing : Pairing n,
        pairing.weight s *
          ∏ pr ∈ pairing.pairs, data.pairValue (C pr.1) (C pr.2) := by
  simpa [toExpectationPairingRecursion] using
    (data.toExpectationPairingRecursion.expectation_eq_sum_pairing n C hC)

end ConvergenceAwarePairingRecursion

end Bosonic
end SecondQuantization
