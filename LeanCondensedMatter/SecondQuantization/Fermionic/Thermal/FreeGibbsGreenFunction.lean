import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint

set_option linter.style.header false

/-!
# Closed-form free Gibbs Green function

The finite free-fermion imaginary-time Green function is evaluated using the canonical density
state and the two-point contractions in `FreeGibbsContraction`. At equal times, the convention
`θ(0) = 1/2` gives a value distinct from both one-sided limits.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The physical free Gibbs Green function
`G₀,ᵢⱼ(τ, τ') = -Tr(ρ₀,β Tτ cᵢ(τ)cⱼ†(τ'))`. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - (freeGibbsDensityOperator ε β).expectation
      (Common.finiteHilbertOperatorAlgEquiv (twoPointTimeOrderedProduct ε i j τ τ'))

/-! ## Closed forms of the free thermal Green function -/

/-- `G₀,ᵢᵢ(τ, τ')` for `τ' < τ`. -/
theorem freeGibbsGreenFunction_of_gt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ' < τ) :
    freeGibbsGreenFunction ε β i i τ τ' =
      - (Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1))) := by
  rw [freeGibbsGreenFunction, twoPointTimeOrderedProduct_of_gt ε i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    map_smul, map_smul, smul_eq_mul,
    freeGibbsDensityOperator_expectation_annihilate_comp_create, ite_eq_left rfl]
  rw [show Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * Complex.exp ((τ' : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- `G₀,ᵢᵢ(τ, τ')` for `τ < τ'`. -/
theorem freeGibbsGreenFunction_of_lt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ < τ') :
    freeGibbsGreenFunction ε β i i τ τ' =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)) := by
  rw [freeGibbsGreenFunction, twoPointTimeOrderedProduct_of_lt ε i i h, Common.Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one, neg_one_smul,
    map_neg, map_neg, neg_neg,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    map_smul, map_smul, smul_eq_mul,
    freeGibbsDensityOperator_expectation_create_comp_annihilate, ite_eq_left rfl]
  rw [show Complex.exp ((τ' : ℂ) * (ε i : ℂ)) * Complex.exp (-(τ : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- `G₀,ᵢᵢ(τ, τ)` with the symmetric equal-time convention `θ(0) = 1/2`. -/
theorem freeGibbsGreenFunction_self_time_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) (τ : ℝ) :
    freeGibbsGreenFunction ε β i i τ τ =
      1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) - (2 : ℂ)⁻¹ := by
  rw [freeGibbsGreenFunction, twoPointTimeOrderedProduct_self_time, Common.Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.exp_add,
    show -(τ : ℂ) * (ε i : ℂ) + (τ : ℂ) * (ε i : ℂ) = 0 by ring,
    show (τ : ℂ) * (ε i : ℂ) + -(τ : ℂ) * (ε i : ℂ) = 0 by ring, Complex.exp_zero, one_smul]
  simp only [map_smul, map_add]
  rw [freeGibbsDensityOperator_expectation_annihilate_comp_create,
    freeGibbsDensityOperator_expectation_create_comp_annihilate]
  simp only [smul_eq_mul, one_mul, neg_mul]
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
    simpa [Common.Statistics.zetaInt_fermion, add_comm] using
      (one_sub_zetaInt_fermion_mul_exp_ne_zero β (ε i))
  simp only [ite_true]
  field_simp
  ring

/-- `G₀,ᵢⱼ(τ, τ') = 0` for `i ≠ j`, at arbitrary imaginary times. -/
theorem freeGibbsGreenFunction_of_ne (ε : Mode → ℝ) (β : ℝ) {i j : Mode} (hij : i ≠ j)
    (τ τ' : ℝ) : freeGibbsGreenFunction ε β i j τ τ' = 0 := by
  rw [freeGibbsGreenFunction]
  unfold twoPointTimeOrderedProduct Common.timeOrderedProduct
  rw [imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
  split_ifs with hτ hτ'
  · simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul]
    rw [freeGibbsDensityOperator_expectation_annihilate_comp_create,
      ite_eq_right hij]
    simp
  · simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul]
    rw [freeGibbsDensityOperator_expectation_create_comp_annihilate,
      ite_eq_right hij]
    simp
  · simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul, map_add]
    rw [freeGibbsDensityOperator_expectation_annihilate_comp_create,
      freeGibbsDensityOperator_expectation_create_comp_annihilate]
    simp [hij]
end Fermionic
end SecondQuantization
