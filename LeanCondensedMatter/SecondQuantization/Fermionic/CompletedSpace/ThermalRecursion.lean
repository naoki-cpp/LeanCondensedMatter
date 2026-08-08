import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalFirstPair
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalPeelIndexed

set_option linter.style.header false

/-!
# Completed fermionic Gibbs pairing recursion

This file discharges the generic `ExpectationPairingRecursion` contract for the completed free
fermionic Gibbs state.  Completed-space CAR, KMS rotation, and Gibbs summability are used only to
prove the first-pair recurrence; the arbitrary-length pairing induction remains in the common
implementation-independent layer.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory
open Combinatorics

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- The completed free-fermion Gibbs expectation as an implementation of the generic
Bloch--de Dominicis pairing-recursion contract. -/
noncomputable def completedFreeGibbsExpectationRecursion
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) :
    Common.BlochDeDominicis.ExpectationPairingRecursion
      (CompletedThermalLadder Mode) Common.Statistics.fermion where
  expectation := completedFreeGibbsExpectation ε β hsum
  pairValue := fun C D => completedFreeGibbsExpectation ε β hsum [C, D]
  admissible := completedFreeGibbsAdmissible ε β
  expectation_nil := completedFreeGibbsExpectation_nil ε β hsum
  admissible_erase := completedFreeGibbsAdmissible_erase ε β
  expectation_succ := by
    intro n C hC
    rw [List.ofFn_succ]
    calc
      completedFreeGibbsExpectation ε β hsum
          (C 0 :: List.ofFn fun i : Fin (2 * n + 1) => C i.succ) =
        ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
          (completedFreeGibbsDensityOperator ε β hsum).expectation
            (thermalPeelSum (C 0) (List.ofFn fun i : Fin (2 * n + 1) => C i.succ)) :=
        completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
          ε β hsum n (C 0) (List.ofFn fun i : Fin (2 * n + 1) => C i.succ)
            (by simp) (hC 0)
      _ = ∑ j : Fin (2 * n + 1),
          (Common.Statistics.fermion.zetaInt : ℂ) ^ (j : ℕ) *
            completedFreeGibbsExpectation ε β hsum [C 0, C j.succ] *
              completedFreeGibbsExpectation ε β hsum
                (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
        rw [completedFreeGibbsExpectation_thermalPeelSum_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [List.length_ofFn, List.getElem_ofFn]
        rw [List.eraseIdx_ofFn_eq_ofFn_succAbove]
        have hpair := completedFreeGibbsExpectation_pair_eq
          ε β hsum (C 0) (C j.succ) (hC 0)
        rw [hpair]
        simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]
        ring

/-- Completed free-fermion Bloch--de Dominicis expansion obtained by feeding the completed Gibbs
recursion data into the common pairing induction. -/
theorem completedFreeGibbsExpectation_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (n : ℕ) (C : Fin (2 * n) → CompletedThermalLadder Mode)
    (hC : completedFreeGibbsAdmissible ε β n C) :
    completedFreeGibbsExpectation ε β hsum (List.ofFn C) =
      ∑ pairing : Pairing n,
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs,
            completedFreeGibbsExpectation ε β hsum [C pr.1, C pr.2] := by
  simpa [completedFreeGibbsExpectationRecursion] using
    (Common.BlochDeDominicis.ExpectationPairingRecursion.expectation_eq_sum_pairing
      (completedFreeGibbsExpectationRecursion ε β hsum) n C hC)

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
