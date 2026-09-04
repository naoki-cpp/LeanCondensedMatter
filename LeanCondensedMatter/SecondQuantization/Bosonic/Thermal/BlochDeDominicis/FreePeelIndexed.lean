import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeKMSRotation
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Indexed free-boson thermal peel

This file rewrites the recursive CCR peel from `OperatorPeel` as the finite position-indexed sum
used by the Bloch--de Dominicis first-pair recurrence.  Unlike the fermionic case there is no
crossing sign: every exchange has bosonic statistic factor `1`.

The second half proves that the entire peel belongs to the explicit free-Gibbs domain under the
usual positive one-mode Boltzmann exponents, and that its normalized expectation is the finite sum
of the expectations of the pair-deleted ordered products.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

namespace FreeThermalField

/-- Individual bosonic CCR peel terms, one for each field in the tail. -/
noncomputable def operatorPeelTerms (C₁ : FreeThermalField Mode) :
    List (FreeThermalField Mode) →
      List (FockSpace Mode →ₗ[ℂ] FockSpace Mode)
  | [] => []
  | D :: t =>
      (C₁.exchangeValue D • orderedProduct t) ::
        (operatorPeelTerms C₁ t).map (fun A => D.operator.comp A)

/-- The recursive bosonic peel is the sum of its individual terms. -/
theorem operatorPeelSum_eq_operatorPeelTerms_sum
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    C₁.operatorPeelSum l = (C₁.operatorPeelTerms l).sum := by
  induction l with
  | nil =>
      simp [FreeThermalField.operatorPeelSum, operatorPeelTerms,
        Common.BlochDeDominicis.operatorPeelSum]
  | cons D t ih =>
      have hfun :
          (fun A : FockSpace Mode →ₗ[ℂ] FockSpace Mode => D.operator.comp A) =
            fun A => (LinearMap.compRight ℂ D.operator) A := by
        rfl
      have hmap :
          ((C₁.operatorPeelTerms t).map (fun A => D.operator.comp A)).sum =
            D.operator.comp (C₁.operatorPeelTerms t).sum := by
        rw [hfun]
        exact
          (map_list_sum (LinearMap.compRight ℂ D.operator) (C₁.operatorPeelTerms t)).symm
      rw [operatorPeelTerms, List.sum_cons, hmap, ← ih]
      unfold FreeThermalField.operatorPeelSum
      rw [Common.BlochDeDominicis.operatorPeelSum]
      simp only [one_smul]
      rw [← orderedProduct_eq_common_operatorProduct]

/-- Closed position-indexed form of the bosonic CCR peel terms. -/
theorem operatorPeelTerms_eq_ofFn
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    C₁.operatorPeelTerms l =
      List.ofFn (fun j : Fin l.length =>
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j)) := by
  induction l with
  | nil => simp [operatorPeelTerms]
  | cons D t ih =>
      rw [List.ofFn_succ, operatorPeelTerms]
      simp only [Fin.val_zero, List.getElem_cons_zero, List.eraseIdx_cons_zero]
      congr 1
      rw [ih, List.map_ofFn]
      congr 1
      funext i
      change D.operator.comp
          (C₁.exchangeValue (t[(i : ℕ)]'i.isLt) • orderedProduct (t.eraseIdx i)) =
        C₁.exchangeValue
            (((D :: t))[((i.succ : Fin (t.length + 1)) : ℕ)]'
              (i.succ : Fin (t.length + 1)).isLt) •
          orderedProduct ((D :: t).eraseIdx (i.succ : Fin (t.length + 1)))
      simp only [Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ,
        FreeThermalField.orderedProduct]
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable [Fintype Mode]

/-- The whole finite CCR peel is in the convergence-aware free-Gibbs domain. -/
theorem operatorPeelSum_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    C₁.operatorPeelSum l ∈ freeGibbsDomain ε β := by
  rw [operatorPeelSum_eq_operatorPeelTerms_sum, operatorPeelTerms_eq_ofFn,
    List.sum_ofFn]
  exact Submodule.sum_mem (freeGibbsDomain ε β) fun j _ =>
    (freeGibbsDomain ε β).smul_mem _
      (FreeThermalField.orderedProduct_mem_freeGibbsDomain ε β hpos (l.eraseIdx j))

/-- Expectation of the bosonic CCR peel as a finite sum over the removed tail position. -/
theorem freeGibbsExpectation_operatorPeelSum_eq_sum
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    freeGibbsExpectation ε β (C₁.operatorPeelSum l) =
      ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) *
          freeGibbsExpectation ε β (orderedProduct (l.eraseIdx j)) := by
  rw [operatorPeelSum_eq_operatorPeelTerms_sum, operatorPeelTerms_eq_ofFn,
    List.sum_ofFn]
  let terms : Fin l.length → freeGibbsDomain ε β := fun j =>
    ⟨C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j),
      (freeGibbsDomain ε β).smul_mem _
        (FreeThermalField.orderedProduct_mem_freeGibbsDomain ε β hpos (l.eraseIdx j))⟩
  have hcoe :
      ((↑(∑ j, terms j) : FockSpace Mode →ₗ[ℂ] FockSpace Mode)) =
        ∑ j : Fin l.length,
          C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j) := by
    rw [Submodule.coe_sum]
  rw [← hcoe]
  have hmap :
      freeGibbsExpectation ε β
          ((∑ j, terms j : freeGibbsDomain ε β).1) =
        ∑ j, freeGibbsExpectation ε β (terms j).1 := by
    change (freeGibbsExpectationLinear ε β) (∑ j, terms j) =
      ∑ j, (freeGibbsExpectationLinear ε β) (terms j)
    simpa using map_sum (freeGibbsExpectationLinear ε β) terms Finset.univ
  calc
    freeGibbsExpectation ε β
        ((∑ j, terms j : freeGibbsDomain ε β).1) =
        ∑ j, freeGibbsExpectation ε β (terms j).1 := hmap
    _ = ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) *
          freeGibbsExpectation ε β (orderedProduct (l.eraseIdx j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change freeGibbsExpectation ε β
          (C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j)) = _
      rw [freeGibbsExpectation_smul]

end FreeThermalField

end
end Bosonic
end SecondQuantization
