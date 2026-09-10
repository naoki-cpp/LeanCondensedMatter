import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering

set_option linter.style.header false

/-!
# Same-type weighted contractions vanish

The algebraic particle-number selection rule in
`Fermionic/Algebra/ParticleNumberCharge.lean` proves that products of two annihilation operators or
two creation operators have zero diagonal occupation-basis coefficients. This module lifts those
statements through an arbitrary normalized occupation-diagonal weight and then through free
imaginary-time evolution and fermionic time ordering.

Thus

`⟨T_τ[c_i(τ) c_j(τ')]⟩_w = 0`, `⟨T_τ[c_i†(τ) c_j†(τ')]⟩_w = 0`

for every occupation-diagonal weight `w`. The conclusion is specific to number-conserving diagonal
states: anomalous contractions need not vanish in non-number-conserving quasi-free states such as
Bogoliubov states.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Vanishing for evolved, time-ordered weighted two-point functionals -/

/-- **`⟨T_τ[c_i(τ) c_j(τ')]⟩_w = 0`** for any occupation-diagonal weight `w`. -/
theorem normalizedWeightedDiagonal_timeOrderedProduct_annihilate_annihilate (ε : Mode → ℝ)
    (w : Occupation Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    Common.normalizedWeightedDiagonal w
      (Common.timeOrderedProduct Common.Statistics.fermion
        (imaginaryTimeEvolve ε τ (annihilate i)) (imaginaryTimeEvolve ε τ' (annihilate j)) τ τ')
      = 0 := by
  have hdiag (a b : Mode) :
      Common.normalizedWeightedDiagonal w ((annihilate a).comp (annihilate b)) = 0 :=
    Common.normalizedWeightedDiagonal_eq_zero_of_matrixCoeff_self_eq_zero w _
      (matrixCoeff_annihilate_comp_annihilate a b)
  rw [imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_annihilate]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [Common.timeOrderedProduct_of_gt Common.Statistics.fermion _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, Common.normalizedWeightedDiagonal_smul,
      hdiag i j]
  · subst h
    rw [Common.timeOrderedProduct_self_time Common.Statistics.fermion]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_add, Common.normalizedWeightedDiagonal_neg,
      hdiag i j, hdiag j i]
  · rw [Common.timeOrderedProduct_of_lt Common.Statistics.fermion _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_neg, hdiag j i]

/-- **`⟨T_τ[c_i†(τ) c_j†(τ')]⟩_w = 0`**, the creation-side counterpart of
`normalizedWeightedDiagonal_timeOrderedProduct_annihilate_annihilate`. -/
theorem normalizedWeightedDiagonal_timeOrderedProduct_create_create (ε : Mode → ℝ)
    (w : Occupation Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    Common.normalizedWeightedDiagonal w
      (Common.timeOrderedProduct Common.Statistics.fermion
        (imaginaryTimeEvolve ε τ (create i)) (imaginaryTimeEvolve ε τ' (create j)) τ τ')
      = 0 := by
  have hdiag (a b : Mode) :
      Common.normalizedWeightedDiagonal w ((create a).comp (create b)) = 0 :=
    Common.normalizedWeightedDiagonal_eq_zero_of_matrixCoeff_self_eq_zero w _
      (matrixCoeff_create_comp_create a b)
  rw [imaginaryTimeEvolve_create, imaginaryTimeEvolve_create]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [Common.timeOrderedProduct_of_gt Common.Statistics.fermion _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, Common.normalizedWeightedDiagonal_smul,
      hdiag i j]
  · subst h
    rw [Common.timeOrderedProduct_self_time Common.Statistics.fermion]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_add, Common.normalizedWeightedDiagonal_neg,
      hdiag i j, hdiag j i]
  · rw [Common.timeOrderedProduct_of_lt Common.Statistics.fermion _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_neg, hdiag j i]

end Fermionic
end SecondQuantization
