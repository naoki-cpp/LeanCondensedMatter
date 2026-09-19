import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeFirstPair
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete free-boson Gibbs pairing recursion

This file closes the B1 analytic gap for the free bosonic Bloch--de Dominicis line.  The arbitrary
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
  have hlen : l.length = 2 * n + 1 := by
    rw [hl]
    simp
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
      have hreindex :
          (∑ i : Fin l.length,
            ((C 0).kmsFactor ε β / ((C 0).kmsFactor ε β - 1)) *
              ((C 0).exchangeValue (l[(i : ℕ)]'i.isLt) *
                freeGibbsExpectation ε β (orderedProduct (l.eraseIdx i)))) =
            ∑ j : Fin (2 * n + 1),
              ((C 0).kmsFactor ε β / ((C 0).kmsFactor ε β - 1)) *
                ((C 0).exchangeValue (C j.succ) *
                  freeGibbsExpectation ε β (orderedProduct (l.eraseIdx j))) := by
        rw [← Equiv.sum_comp (finCongr hlen.symm)]
        apply Finset.sum_congr rfl
        intro j _
        simp only [finCongr_apply, Fin.val_cast, hl, List.getElem_ofFn]
      rw [hreindex]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hl, List.eraseIdx_ofFn_eq_ofFn_succAbove]
      have hpair := kmsRatio_mul_exchangeValue_eq_freeThermalPairValue
        ε β hpos (C 0) (C j.succ)
      rw [← hpair]
      ring

end FreeThermalField

/-- Concrete convergence-aware free-boson pairing recursion.  Every finite ordered field family is
admissible because #868 proves its free-Gibbs summability under `hpos`. -/
noncomputable def concreteFreeGibbsPairingRecursion
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    ConvergenceAwarePairingRecursion
      (FockSpace Mode →ₗ[ℂ] FockSpace Mode) (FreeThermalField Mode) .boson :=
  freeGibbsPairingRecursion ε β hpos
    (fun _ _ => True)
    (fun _ C _ =>
      FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos (List.ofFn C))
    (fun _ _ _ _ => trivial)
    (by
      intro n C _
      have hfull := FreeThermalField.freeGibbsSummable_orderedProduct
        ε β hpos (List.ofFn C)
      rw [freeGibbsFunctional_value_of_summable ε β hpos hfull]
      have hrec := FreeThermalField.freeGibbsExpectation_firstPair_recursion
        ε β hpos n C
      calc
        freeGibbsExpectation ε β (FreeThermalField.orderedProduct (List.ofFn C)) =
            ∑ j : Fin (2 * n + 1),
              freeThermalPairValue ε β (C 0) (C j.succ) *
                freeGibbsExpectation ε β
                  (FreeThermalField.orderedProduct
                    (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))) := hrec
        _ = ∑ j : Fin (2 * n + 1),
              freeThermalPairValue ε β (C 0) (C j.succ) *
                (freeGibbsFunctional ε β hpos).value
                  (FreeThermalField.orderedProduct
                    (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))) := by
          apply Finset.sum_congr rfl
          intro j _
          have htail := FreeThermalField.freeGibbsSummable_orderedProduct
            ε β hpos
              (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))
          rw [freeGibbsFunctional_value_of_summable ε β hpos htail])

/-- Fully concrete free-boson Bloch--de Dominicis/Wick pairing expansion.  The only analytic
hypothesis is positivity of every one-mode Boltzmann exponent. -/
theorem freeGibbsExpectation_eq_sum_pairing_concrete
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (n : ℕ) (C : Fin (2 * n) → FreeThermalField Mode) :
    freeGibbsExpectation ε β (FreeThermalField.orderedProduct (List.ofFn C)) =
      ∑ pairing : Pairing n,
        pairing.weight .boson *
          ∏ pr ∈ pairing.pairs, freeThermalPairValue ε β (C pr.1) (C pr.2) := by
  let data := concreteFreeGibbsPairingRecursion ε β hpos
  have h := data.toExpectationPairingRecursion.expectation_eq_sum_pairing n C trivial
  change
    (freeGibbsFunctional ε β hpos).value
        (FreeThermalField.orderedProduct (List.ofFn C)) =
      ∑ pairing : Pairing n,
        pairing.weight .boson *
          ∏ pr ∈ pairing.pairs, freeThermalPairValue ε β (C pr.1) (C pr.2) at h
  have hmem := FreeThermalField.freeGibbsSummable_orderedProduct
    ε β hpos (List.ofFn C)
  rw [freeGibbsFunctional_value_of_summable ε β hpos hmem] at h
  exact h

end
end Bosonic
end SecondQuantization
