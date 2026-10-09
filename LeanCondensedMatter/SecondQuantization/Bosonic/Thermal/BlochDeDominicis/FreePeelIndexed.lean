import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeKMSRotation
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OperatorPeel
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

variable [Fintype Mode]

/-- The whole finite CCR peel is in the convergence-aware free-Gibbs domain. -/
theorem operatorPeelSum_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    C₁.operatorPeelSum l ∈ freeGibbsDomain ε β := by
  have h : C₁.operatorPeelSum l =
      ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j) := by
    simpa only [operatorPeelSum, one_pow, one_mul, orderedProduct] using
      ScalarExchange.peelSum_eq_sum operator exchangeValue (1 : ℂ) C₁ l
  rw [h, mem_freeGibbsDomain_iff]
  exact freeGibbsSummable_sum ε β
    (fun j : Fin l.length =>
      C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j))
    (fun j => freeGibbsSummable_smul ε β _
      (FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos (l.eraseIdx j)))

/-- Expectation of the bosonic CCR peel as a finite sum over the removed tail position. -/
theorem freeGibbsExpectation_operatorPeelSum_eq_sum
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (C₁ : FreeThermalField Mode) (l : List (FreeThermalField Mode)) :
    freeGibbsExpectation ε β (C₁.operatorPeelSum l) =
      ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) *
          freeGibbsExpectation ε β (orderedProduct (l.eraseIdx j)) := by
  have h : C₁.operatorPeelSum l =
      ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j) := by
    simpa only [operatorPeelSum, one_pow, one_mul, orderedProduct] using
      ScalarExchange.peelSum_eq_sum operator exchangeValue (1 : ℂ) C₁ l
  rw [h]
  calc
    freeGibbsExpectation ε β
        (∑ j : Fin l.length,
          C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j)) =
        ∑ j : Fin l.length,
          freeGibbsExpectation ε β
            (C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j)) :=
      freeGibbsExpectation_sum_of_summable ε β
        (fun j : Fin l.length =>
          C₁.exchangeValue (l[(j : ℕ)]'j.isLt) • orderedProduct (l.eraseIdx j))
        (fun j => freeGibbsSummable_smul ε β _
          (FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos (l.eraseIdx j)))
    _ = ∑ j : Fin l.length,
        C₁.exchangeValue (l[(j : ℕ)]'j.isLt) *
          freeGibbsExpectation ε β (orderedProduct (l.eraseIdx j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [freeGibbsExpectation_smul]

end FreeThermalField

end
end Bosonic
end SecondQuantization
