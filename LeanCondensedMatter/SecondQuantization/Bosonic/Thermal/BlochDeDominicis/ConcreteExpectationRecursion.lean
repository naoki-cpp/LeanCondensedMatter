import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeFirstPair
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn
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
theorem freeGibbsExpectation_firstPair_recursion
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (n : ℕ) (C : Fin (2 * (n + 1)) → FreeThermalField Mode) :
    freeGibbsExpectation ε β (orderedProduct (List.ofFn C)) =
      ∑ j : Fin (2 * n + 1),
        freeThermalPairValue ε β (C 0) (C j.succ) *
          freeGibbsExpectation ε β
            (orderedProduct
              (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))) := by
  rw [List.ofFn_succ]
  set l : List (FreeThermalField Mode) :=
    List.ofFn (fun i : Fin (2 * n + 1) => C i.succ) with hl
  calc
    freeGibbsExpectation ε β (orderedProduct (C 0 :: l)) =
        ((C 0).kmsFactor ε β / ((C 0).kmsFactor ε β - 1)) *
          freeGibbsExpectation ε β ((C 0).operatorPeelSum l) :=
      freeGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum ε β hpos (C 0) l
    _ = ∑ j : Fin (2 * n + 1),
        freeThermalPairValue ε β (C 0) (C j.succ) *
          freeGibbsExpectation ε β
            (orderedProduct
              (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))) := by
      rw [freeGibbsExpectation_operatorPeelSum_eq_sum ε β hpos (C 0) l,
        Finset.mul_sum]
      rw [hl, List.sum_getElem_eraseIdx_ofFn
        (fun i : Fin (2 * n + 1) => C i.succ)
        (fun _ field rest =>
          ((C 0).kmsFactor ε β / ((C 0).kmsFactor ε β - 1)) *
            ((C 0).exchangeValue field * freeGibbsExpectation ε β (orderedProduct rest)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hpair := kmsRatio_mul_exchangeValue_eq_freeThermalPairValue
        ε β hpos (C 0) (C j.succ)
      rw [← hpair]
      ring

end FreeThermalField

/-- File-local realization of the Common pairing recursion using the actual free-Gibbs expectation.
Every finite field product is summable under `hpos`; the first-pair theorem supplies the analytic
KMS/exchange recurrence without transporting values through an additional totalization. -/
private noncomputable def concreteFreeGibbsPairingRecursion
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    Common.BlochDeDominicis.ExpectationPairingRecursion (FreeThermalField Mode) .boson where
  expectation := fun fields => freeGibbsExpectation ε β (FreeThermalField.orderedProduct fields)
  pairValue := freeThermalPairValue ε β
  admissible := fun _ _ => True
  expectation_nil := by
    rw [FreeThermalField.orderedProduct_nil]
    exact freeGibbsExpectation_id ε β hpos
  admissible_erase := fun _ _ _ _ => trivial
  expectation_succ := by
    intro n C _
    simpa only [Statistics.zetaInt_boson, Int.cast_one, one_pow, one_mul] using
      FreeThermalField.freeGibbsExpectation_firstPair_recursion ε β hpos n C

/-- Fully concrete free-boson Bloch--de Dominicis/Wick pairing expansion.  The only analytic
hypothesis is positivity of every one-mode Boltzmann exponent. -/
theorem freeGibbsExpectation_eq_sum_pairing_concrete
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (n : ℕ) (C : Fin (2 * n) → FreeThermalField Mode) :
    freeGibbsExpectation ε β (FreeThermalField.orderedProduct (List.ofFn C)) =
      ∑ pairing : Pairing n,
        pairing.weight .boson *
          ∏ pr ∈ pairing.pairs, freeThermalPairValue ε β (C pr.1) (C pr.2) := by
  exact (concreteFreeGibbsPairingRecursion ε β hpos).bloch_de_dominicis n C trivial

end
end Bosonic
end SecondQuantization
