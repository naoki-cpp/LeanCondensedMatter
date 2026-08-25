import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeKMSRotation
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
      have hmap : ∀ L : List (FockSpace Mode →ₗ[ℂ] FockSpace Mode),
          (L.map (fun A => D.operator.comp A)).sum = D.operator.comp L.sum := by
        intro L
        induction L with
        | nil => simp
        | cons A T ihT =>
            rw [List.map_cons, List.sum_cons, List.sum_cons, ihT]
            apply LinearMap.ext
            intro x
            simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
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

omit [Fintype Mode] in
/-- Finite additivity of the normalized free-Gibbs expectation on explicitly summable terms. -/
private theorem freeGibbsExpectation_finset_sum
    {ι : Type*}
    (ε : Mode → ℝ) (β : ℝ) (s : Finset ι)
    (f : ι → (FockSpace Mode →ₗ[ℂ] FockSpace Mode))
    (hf : ∀ i ∈ s, f i ∈ freeGibbsDomain ε β) :
    freeGibbsExpectation ε β (∑ i ∈ s, f i) =
      ∑ i ∈ s, freeGibbsExpectation ε β (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have hzero : freeGibbsExpectation ε β
          (0 : FockSpace Mode →ₗ[ℂ] FockSpace Mode) = 0 := by
        simpa using freeGibbsExpectation_smul ε β (0 : ℂ)
          (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
      simpa [hzero]
  | @insert a s ha ih =>
      intro hf
      have hfa : f a ∈ freeGibbsDomain ε β := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ∈ freeGibbsDomain ε β := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      have hsum : (∑ i ∈ s, f i) ∈ freeGibbsDomain ε β :=
        Submodule.sum_mem (freeGibbsDomain ε β) hfs
      rw [Finset.sum_insert ha, freeGibbsExpectation_add ε β hfa hsum,
        Finset.sum_insert ha, ih hfs]

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
  rw [freeGibbsExpectation_finset_sum ε β Finset.univ
    (fun j : Fin l.length =>
      C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j))]
  · apply Finset.sum_congr rfl
    intro j _
    rw [freeGibbsExpectation_smul]
  · intro j _
    exact (freeGibbsDomain ε β).smul_mem _
      (FreeThermalField.orderedProduct_mem_freeGibbsDomain ε β hpos (l.eraseIdx j))

end FreeThermalField

end
end Bosonic
end SecondQuantization
