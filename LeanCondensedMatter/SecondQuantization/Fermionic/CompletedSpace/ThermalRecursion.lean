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
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
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
    set l : List (CompletedThermalLadder Mode) :=
      List.ofFn (fun i : Fin (2 * n + 1) => C i.succ) with hl
    have hlen : l.length = 2 * n + 1 := by
      rw [hl]
      simp
    calc
      completedFreeGibbsExpectation ε β hsum (C 0 :: l) =
        ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
          (purePointGibbsDensityOperator completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum).expectation
            (thermalPeelSum (C 0) l) :=
        completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
          ε β hsum n (C 0) l hlen (hC 0)
      _ = ∑ j : Fin (2 * n + 1),
          (Common.Statistics.fermion.zetaInt : ℂ) ^ (j : ℕ) *
            completedFreeGibbsExpectation ε β hsum [C 0, C j.succ] *
              completedFreeGibbsExpectation ε β hsum
                (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
        rw [completedFreeGibbsExpectation_thermalPeelSum_eq_sum, Finset.mul_sum]
        let hcast : Fin l.length ≃ Fin (2 * n + 1) :=
          ⟨Fin.cast hlen, Fin.cast hlen.symm, fun i => rfl, fun i => rfl⟩
        have hreindex :
            (∑ i : Fin l.length,
              ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
                (((-1 : ℂ) ^ (i : ℕ)) * (C 0).anticommutatorValue (l[(i : ℕ)]'i.isLt) *
                  completedFreeGibbsExpectation ε β hsum (l.eraseIdx i))) =
              ∑ j : Fin (2 * n + 1),
                ((C 0).gibbsFactor ε β / ((1 : ℂ) + (C 0).gibbsFactor ε β)) *
                  (((-1 : ℂ) ^ (j : ℕ)) * (C 0).anticommutatorValue (C j.succ) *
                    completedFreeGibbsExpectation ε β hsum (l.eraseIdx j)) :=
          Fintype.sum_equiv hcast _ _ fun i => by
            have hv : ((hcast i : Fin (2 * n + 1)) : ℕ) = (i : ℕ) := by
              change ((Fin.cast hlen i : Fin (2 * n + 1)) : ℕ) = (i : ℕ)
              rfl
            simp only [hv]
            simp only [hl, List.getElem_ofFn]
            congr 4
        rw [hreindex]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hl, List.eraseIdx_ofFn_eq_ofFn_succAbove]
        have hpair := completedFreeGibbsExpectation_pair_eq
          ε β hsum (C 0) (C j.succ) (hC 0)
        rw [hpair]
        simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]
        ring

/-- Completed free-fermion Bloch--de Dominicis expansion obtained by feeding the completed Gibbs
recursion data into the common pairing induction. -/
theorem completedFreeGibbsExpectation_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
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
