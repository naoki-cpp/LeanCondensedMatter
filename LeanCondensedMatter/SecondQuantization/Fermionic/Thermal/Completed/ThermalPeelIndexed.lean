import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalPeel
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Indexed completed fermionic thermal peel

This file rewrites the recursively defined completed CAR peel as the position-indexed finite sum
used by the generic Bloch--de Dominicis first-pair recurrence.  The representation-specific
operator algebra remains here; the pairing induction itself stays in
`Common.BlochDeDominicis.ExpectationPairingRecursion`.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Individual completed CAR peel terms, one for each operator in the tail. -/
noncomputable def thermalPeelTerms (C₁ : CompletedThermalLadder Mode) :
    List (CompletedThermalLadder Mode) →
      List (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
  | [] => []
  | D :: t =>
      (C₁.anticommutatorValue D • operatorProduct t) ::
        (thermalPeelTerms C₁ t).map (fun A => (-1 : ℂ) • (D.operator.comp A))

/-- The recursive completed peel sum is the sum of its individual terms. -/
theorem thermalPeelSum_eq_thermalPeelTerms_sum
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    thermalPeelSum C₁ l = (thermalPeelTerms C₁ l).sum := by
  induction l with
  | nil => simp [thermalPeelSum, thermalPeelTerms]
  | cons D t ih =>
      have hmap :
          ((thermalPeelTerms C₁ t).map (fun A => (-1 : ℂ) • (D.operator.comp A))).sum =
            (-1 : ℂ) • (D.operator.comp (thermalPeelTerms C₁ t).sum) := by
        have h := (map_list_sum
          ((-1 : ℂ) •
            (ContinuousLinearMap.compL ℂ
              (CompletedFockSpace Mode) (CompletedFockSpace Mode) (CompletedFockSpace Mode)
              D.operator))
          (thermalPeelTerms C₁ t)).symm
        simpa only [smul_apply, ContinuousLinearMap.compL_apply] using h
      rw [thermalPeelSum, thermalPeelTerms, List.sum_cons, hmap, ← ih]
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply]
      module

/-- Closed position-indexed form of the completed CAR peel terms. -/
theorem thermalPeelTerms_eq_ofFn
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    thermalPeelTerms C₁ l =
      List.ofFn (fun j : Fin l.length =>
        (((-1 : ℂ) ^ (j : ℕ)) * C₁.anticommutatorValue (l[(j : ℕ)]'j.isLt)) •
          operatorProduct (l.eraseIdx j)) := by
  induction l with
  | nil => simp [thermalPeelTerms]
  | cons D t ih =>
      rw [List.ofFn_succ, thermalPeelTerms]
      simp only [Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero,
        List.eraseIdx_cons_zero]
      congr 1
      rw [ih, List.map_ofFn]
      congr 1
      funext i
      change (-1 : ℂ) •
          (D.operator.comp
            ((((-1 : ℂ) ^ (i : ℕ)) *
                C₁.anticommutatorValue (t[(i : ℕ)]'i.isLt)) •
              operatorProduct (t.eraseIdx i))) =
        (((-1 : ℂ) ^ ((i.succ : Fin (t.length + 1)) : ℕ)) *
            C₁.anticommutatorValue
              (((D :: t))[((i.succ : Fin (t.length + 1)) : ℕ)]'
                (i.succ : Fin (t.length + 1)).isLt)) •
          operatorProduct ((D :: t).eraseIdx (i.succ : Fin (t.length + 1)))
      simp only [Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ,
        operatorProduct_cons, pow_succ]
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul]
      module

/-- Expectation of the completed CAR peel as an indexed finite sum over the removed tail position. -/
theorem completedFreeGibbsExpectation_thermalPeelSum_eq_sum
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C₁ : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
      (fermionEnergy ε) β hsum).expectation (thermalPeelSum C₁ l) =
      ∑ j : Fin l.length,
        ((-1 : ℂ) ^ (j : ℕ)) * C₁.anticommutatorValue (l[(j : ℕ)]'j.isLt) *
          completedFreeGibbsExpectation ε β hsum (l.eraseIdx j) := by
  have hmap : ∀ L : List (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode),
      (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation L.sum =
        (L.map (purePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β hsum).expectation).sum := by
    intro L
    exact map_list_sum
      (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation L
  rw [thermalPeelSum_eq_thermalPeelTerms_sum, thermalPeelTerms_eq_ofFn, hmap,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp]
  rw [map_smul]
  simp only [smul_eq_mul, completedFreeGibbsExpectation]

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
