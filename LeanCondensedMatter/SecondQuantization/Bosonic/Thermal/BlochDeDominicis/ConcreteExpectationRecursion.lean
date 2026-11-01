import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeFirstPair
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete free-boson Gibbs pairing recursion

This module constructs the free bosonic Bloch--de Dominicis recursion from its analytic proofs.  The arbitrary
fixed-length ordered products are summable, the CCR peel has a finite indexed form, and KMS rotation
solves the wrapped term.  These ingredients produce the concrete first-pair recurrence with
`freeThermalPairValue`, then instantiate the representation-independent Common pairing recursion.

No finite occupation-basis assumption is used.  Admissibility is simply `True`: under the explicit
positive one-mode Boltzmann exponent hypothesis every finite free-thermal ordered product is already
in the free-Gibbs domain.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality for the concrete pair kernel. -/
local instance instDecidableEqConcreteExpectationRecursion : DecidableEq Mode := Classical.decEq Mode

namespace FreeThermalField

/-- Concrete normalized free-Gibbs first-pair recurrence for an arbitrary even field family. -/
private theorem grandCanonicalGibbsExpectation_firstPair_recursion
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (n : ℕ) (C : Fin (2 * (n + 1)) → FreeThermalField Mode) :
    grandCanonicalGibbsExpectation ε β μ (orderedProduct (List.ofFn C)) =
      ∑ j : Fin (2 * n + 1),
        freeThermalPairValue (fun i => ε i - μ) β (C 0) (C j.succ) *
          grandCanonicalGibbsExpectation ε β μ
            (orderedProduct
              (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))) := by
  rw [List.ofFn_succ]
  set l : List (FreeThermalField Mode) :=
    List.ofFn (fun i : Fin (2 * n + 1) => C i.succ) with hl
  calc
    grandCanonicalGibbsExpectation ε β μ (orderedProduct (C 0 :: l)) =
        ((C 0).kmsFactor (fun i => ε i - μ) β / ((C 0).kmsFactor (fun i => ε i - μ) β - 1)) *
          grandCanonicalGibbsExpectation ε β μ ((C 0).operatorPeelSum l) :=
      grandCanonicalGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum ε β μ hpos (C 0) l
    _ = ∑ j : Fin (2 * n + 1),
        freeThermalPairValue (fun i => ε i - μ) β (C 0) (C j.succ) *
          grandCanonicalGibbsExpectation ε β μ
            (orderedProduct
              (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))) := by
      rw [grandCanonicalGibbsExpectation_operatorPeelSum_eq_sum ε β μ hpos (C 0) l, hl]
      simpa only [Statistics.zetaInt_boson, Int.cast_one, one_pow, one_mul] using
        (Common.BlochDeDominicis.indexedPeel_sum_eq_firstPair
          (1 : ℂ)
          ((C 0).kmsFactor (fun i => ε i - μ) β / ((C 0).kmsFactor (fun i => ε i - μ) β - 1))
          (fun D => (C 0).exchangeValue D)
          (fun D => freeThermalPairValue (fun i => ε i - μ) β (C 0) D)
          (fun rest => grandCanonicalGibbsExpectation ε β μ (orderedProduct rest))
          (fun i : Fin (2 * n + 1) => C i.succ)
          (fun D => grandCanonicalKmsRatio_mul_exchangeValue_eq_freeThermalPairValue
            ε β μ hpos (C 0) D))

end FreeThermalField

/-- File-local realization of the Common pairing recursion using the actual free-Gibbs expectation.
Every finite field product is summable under `hpos`; the first-pair theorem supplies the analytic
KMS/exchange recurrence without transporting values through an additional totalization. -/
private noncomputable def concreteGrandCanonicalGibbsPairingRecursion
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ)) :
    Common.BlochDeDominicis.ExpectationPairingRecursion (FreeThermalField Mode) .boson where
  expectation := fun fields => grandCanonicalGibbsExpectation ε β μ (FreeThermalField.orderedProduct fields)
  pairValue := freeThermalPairValue (fun i => ε i - μ) β
  admissible := fun _ _ => True
  expectation_nil := by
    rw [FreeThermalField.orderedProduct_nil]
    exact grandCanonicalGibbsExpectation_id ε β μ hpos
  admissible_erase := fun _ _ _ _ => trivial
  expectation_succ := by
    intro n C _
    simpa only [Statistics.zetaInt_boson, Int.cast_one, one_pow, one_mul] using
      FreeThermalField.grandCanonicalGibbsExpectation_firstPair_recursion ε β μ hpos n C

/-- Grand-canonical free-boson Wick/Bloch--de Dominicis factorization at arbitrary chemical
potential. The free-field pairing kernel uses `ε - μ`; the abstract recurrence is applied on this
effective thermal dispersion. This does not assert fixed-particle-number canonical Wick factorization. -/
theorem grandCanonicalGibbsExpectation_eq_sum_pairing_concrete
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (n : ℕ) (C : Fin (2 * n) → FreeThermalField Mode) :
    grandCanonicalGibbsExpectation ε β μ (FreeThermalField.orderedProduct (List.ofFn C)) =
      ∑ pairing : Pairing n,
        pairing.weight .boson *
          ∏ pr ∈ pairing.pairs,
            freeThermalPairValue (fun i => ε i - μ) β (C pr.1) (C pr.2) := by
  exact (concreteGrandCanonicalGibbsPairingRecursion ε β μ hpos).bloch_de_dominicis
    n C trivial

end
end Bosonic
end SecondQuantization
