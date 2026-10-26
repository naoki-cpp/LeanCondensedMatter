import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint

set_option linter.style.header false

/-!
# Finite grand-canonical free Gibbs Green function

The grand-canonical finite-fermion Green function uses Gibbs weights of `H - μ N`
while its imaginary-time fields evolve under the physical Hamiltonian `H`.
The contractions use the explicit-μ finite Gibbs mean and are proven through
the finite/completed bounded-operator Gibbs bridge.
At equal times, `θ(0) = 1/2` gives a value distinct from both one-sided limits.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The free grand-canonical Gibbs Green function
`G₀,ᵢⱼ(τ, τ') = -Tr(ρβ,μ Tτ cᵢ(τ)cⱼ†(τ'))`. -/
noncomputable def grandCanonicalFreeGreenFunction (ε : Mode → ℝ) (β μ : ℝ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - Common.finiteGibbsExpectation
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
      (twoPointTimeOrderedProduct ε i j τ τ')

/-! ## Closed forms of the free thermal Green function -/

/-- `G₀,ᵢᵢ(τ, τ')` for `τ' < τ`. -/
theorem grandCanonicalFreeGreenFunction_of_gt_self (ε : Mode → ℝ) (β μ : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ' < τ) :
    grandCanonicalFreeGreenFunction ε β μ i i τ τ' =
      - (Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1))) := by
  rw [grandCanonicalFreeGreenFunction]
  change -(Common.finiteGibbsExpectationLinearMap
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (twoPointTimeOrderedProduct ε i i τ τ') = _
  have hAC := grandCanonicalFiniteGibbsExpectation_annihilate_comp_create ε β μ i i
  simp only [Common.finiteGibbsExpectation] at hAC
  rw [twoPointTimeOrderedProduct_of_gt ε i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    map_smul, smul_eq_mul,
    hAC, ite_eq_left rfl]
  rw [show Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * Complex.exp ((τ' : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- `G₀,ᵢᵢ(τ, τ')` for `τ < τ'`. -/
theorem grandCanonicalFreeGreenFunction_of_lt_self (ε : Mode → ℝ) (β μ : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ < τ') :
    grandCanonicalFreeGreenFunction ε β μ i i τ τ' =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1)) := by
  rw [grandCanonicalFreeGreenFunction]
  change -(Common.finiteGibbsExpectationLinearMap
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (twoPointTimeOrderedProduct ε i i τ τ') = _
  have hAC := grandCanonicalFiniteGibbsExpectation_annihilate_comp_create ε β μ i i
  simp only [Common.finiteGibbsExpectation] at hAC
  have hCA := grandCanonicalFiniteGibbsExpectation_create_comp_annihilate ε β μ i i
  simp only [Common.finiteGibbsExpectation] at hCA
  rw [twoPointTimeOrderedProduct_of_lt ε i i h, Common.Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one, neg_one_smul,
    map_neg, neg_neg,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    map_smul, smul_eq_mul,
    hCA, ite_eq_left rfl]
  rw [show Complex.exp ((τ' : ℂ) * (ε i : ℂ)) * Complex.exp (-(τ : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- `G₀,ᵢᵢ(τ, τ)` with the symmetric equal-time convention `θ(0) = 1/2`. -/
theorem grandCanonicalFreeGreenFunction_self_time_self (ε : Mode → ℝ) (β μ : ℝ) (i : Mode) (τ : ℝ) :
    grandCanonicalFreeGreenFunction ε β μ i i τ τ =
      1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1) - (2 : ℂ)⁻¹ := by
  rw [grandCanonicalFreeGreenFunction]
  change -(Common.finiteGibbsExpectationLinearMap
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (twoPointTimeOrderedProduct ε i i τ τ) = _
  have hAC := grandCanonicalFiniteGibbsExpectation_annihilate_comp_create ε β μ i i
  simp only [Common.finiteGibbsExpectation] at hAC
  have hCA := grandCanonicalFiniteGibbsExpectation_create_comp_annihilate ε β μ i i
  simp only [Common.finiteGibbsExpectation] at hCA
  rw [twoPointTimeOrderedProduct_self_time, Common.Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.exp_add,
    show -(τ : ℂ) * (ε i : ℂ) + (τ : ℂ) * (ε i : ℂ) = 0 by ring,
    show (τ : ℂ) * (ε i : ℂ) + -(τ : ℂ) * (ε i : ℂ) = 0 by ring, Complex.exp_zero, one_smul]
  simp only [map_smul, map_add]
  rw [hAC, hCA]
  simp only [smul_eq_mul, one_mul, neg_mul]
  have hE : Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1 ≠ 0 := by
    simpa [Common.Statistics.zetaInt_fermion, add_comm] using
      (one_sub_zetaInt_fermion_mul_exp_ne_zero β (ε i - μ))
  simp only [ite_true]
  field_simp
  ring

/-- `G₀,ᵢⱼ(τ, τ') = 0` for `i ≠ j`, at arbitrary imaginary times. -/
theorem grandCanonicalFreeGreenFunction_of_ne (ε : Mode → ℝ) (β μ : ℝ) {i j : Mode} (hij : i ≠ j)
    (τ τ' : ℝ) : grandCanonicalFreeGreenFunction ε β μ i j τ τ' = 0 := by
  rw [grandCanonicalFreeGreenFunction]
  change -(Common.finiteGibbsExpectationLinearMap
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (twoPointTimeOrderedProduct ε i j τ τ') = _
  have hAC := grandCanonicalFiniteGibbsExpectation_annihilate_comp_create ε β μ i j
  simp only [Common.finiteGibbsExpectation] at hAC
  have hCA := grandCanonicalFiniteGibbsExpectation_create_comp_annihilate ε β μ i j
  simp only [Common.finiteGibbsExpectation] at hCA
  unfold twoPointTimeOrderedProduct Common.timeOrderedProduct
  rw [imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
  split_ifs with hτ hτ'
  · simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul]
    rw [hAC, ite_eq_right hij]
    simp
  · simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul]
    rw [hCA, ite_eq_right hij]
    simp
  · simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul, map_add]
    rw [hAC, hCA]
    simp [hij]
end Fermionic
end SecondQuantization
