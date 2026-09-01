import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# Closed-form free Gibbs Green function

This module defines the finite free-fermion imaginary-time Green function directly from the
canonical Gibbs density operator. Coordinate lemmas for off-diagonal mixed contractions remain
private proof infrastructure, while `freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction`
connects the physical definition to the finite occupation-coordinate calculation.

Off-diagonal vanishing of the *mixed* contractions is mode-specific rather than a particle-number
selection rule: those operators have zero total charge, but toggling distinct modes cannot return an
occupation state to itself. At equal times, the project convention `θ(0) = 1/2` gives a value
distinct from both one-sided limits.

The *anomalous* contractions vanish for the opposite reason, a genuine particle-number selection
rule: two creation or two annihilation operators change the particle number by two, and the free
Gibbs state is diagonal in the occupation basis. This is what makes every contraction pair a
creation operator with an annihilation operator.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The physical free Gibbs Green function
`G₀,ᵢⱼ(τ, τ') = -Tr(ρ₀,β Tτ cᵢ(τ)cⱼ†(τ'))`. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - (freeGibbsDensityOperator ε β).expectation
      (Common.finiteHilbertOperator (twoPointTimeOrderedProduct ε i j τ τ'))

/-! ## Private coordinate lemmas for off-diagonal mixed contractions -/

omit [Fintype Mode] in
private theorem matrixCoeff_annihilate_comp_create_of_ne {i j : Mode} (hij : i ≠ j)
    (n : Occupation Mode) :
    Common.matrixCoeff ((annihilate i).comp (create j)) n n = 0 := by
  change ((annihilate i).comp (create j)) (basisState n) n = 0
  by_cases hj : j ∈ n
  · rw [LinearMap.comp_apply, create_basisState_of_mem hj, map_zero]
    simp
  · rw [LinearMap.comp_apply, create_basisState_of_not_mem hj, map_smul]
    by_cases hi : i ∈ insertOccupation j n
    · rw [annihilate_basisState_of_mem hi, smul_smul]
      have hine : i ∈ n := by
        rcases Finset.mem_insert.1 hi with h | h
        · exact absurd h hij
        · exact h
      have hne : removeOccupation i (insertOccupation j n) ≠ n := by
        intro heq
        rw [← heq] at hine
        exact Finset.notMem_erase i (insertOccupation j n) hine
      exact Common.smul_basisState_apply_of_ne _ hne
    · rw [annihilate_basisState_of_not_mem hi, smul_zero]
      simp

omit [Fintype Mode] in
private theorem matrixCoeff_create_comp_annihilate_of_ne {i j : Mode} (hij : i ≠ j)
    (n : Occupation Mode) :
    Common.matrixCoeff ((create j).comp (annihilate i)) n n = 0 := by
  have hanticomm := anticomm_annihilate_create i j
  rw [if_neg hij, anticomm] at hanticomm
  have hzero : ((annihilate i).comp (create j) + (create j).comp (annihilate i))
      (basisState n) = 0 := by rw [hanticomm]; simp
  rw [LinearMap.add_apply] at hzero
  have hcoeff := DFunLike.congr_fun hzero n
  simp only [Finsupp.add_apply, Finsupp.zero_apply] at hcoeff
  have h1 : ((annihilate i).comp (create j)) (basisState n) n = 0 :=
    matrixCoeff_annihilate_comp_create_of_ne hij n
  change ((create j).comp (annihilate i)) (basisState n) n = 0
  linear_combination hcoeff - h1

private theorem normalizedWeightedDiagonal_annihilate_comp_create_of_ne
    (w : Occupation Mode → ℂ) {i j : Mode} (hij : i ≠ j) :
    Common.normalizedWeightedDiagonal w ((annihilate i).comp (create j)) = 0 := by
  rw [Common.normalizedWeightedDiagonal]
  simp [Common.weightedTrace, matrixCoeff_annihilate_comp_create_of_ne hij]

private theorem normalizedWeightedDiagonal_create_comp_annihilate_of_ne
    (w : Occupation Mode → ℂ) {i j : Mode} (hij : i ≠ j) :
    Common.normalizedWeightedDiagonal w ((create j).comp (annihilate i)) = 0 := by
  rw [Common.normalizedWeightedDiagonal]
  simp [Common.weightedTrace, matrixCoeff_create_comp_annihilate_of_ne hij]

omit [LinearOrder Mode] in
private theorem normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation
    (ε : Mode → ℝ) (β : ℝ) (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β) A =
      (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperator A) := by
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β :=
    funext (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β)
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_eq_normalizedWeightedDiagonal, hw]

/-- The density-state Green function agrees with its finite occupation-coordinate evaluation. -/
theorem freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ) :
    freeGibbsGreenFunction ε β i j τ τ' =
      weightedFreeTwoPointFunction ε (freeBoltzmannWeight ε β) i j τ τ' := by
  rw [freeGibbsGreenFunction, weightedFreeTwoPointFunction,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation]

private theorem freeGibbsDensityOperator_expectation_annihilate_comp_create_self
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator ((annihilate i).comp (create i))) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) := by
  rw [← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    annihilate_comp_create_self, Common.normalizedWeightedDiagonal_sub,
    Common.normalizedWeightedDiagonal_id _ (weightSum_freeBoltzmannWeight_ne_zero ε β),
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_numberOperator]
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
    rw [show Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 =
      ((Real.exp (β * ε i) + 1 : ℝ) : ℂ) by push_cast [Complex.ofReal_exp]; ring]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  field_simp
  ring

/-! ## Closed forms of the free thermal Green function -/

/-- `G₀,ᵢᵢ(τ, τ')` for `τ' < τ`. -/
theorem freeGibbsGreenFunction_of_gt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ' < τ) :
    freeGibbsGreenFunction ε β i i τ τ' =
      - (Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1))) := by
  rw [freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction,
    weightedFreeTwoPointFunction_of_gt ε (freeBoltzmannWeight ε β) i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul, Common.normalizedWeightedDiagonal_smul,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_annihilate_comp_create_self]
  rw [show Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * Complex.exp ((τ' : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- `G₀,ᵢᵢ(τ, τ')` for `τ < τ'`. -/
theorem freeGibbsGreenFunction_of_lt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ < τ') :
    freeGibbsGreenFunction ε β i i τ τ' =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)) := by
  rw [freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction,
    weightedFreeTwoPointFunction_of_lt ε (freeBoltzmannWeight ε β) i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    show (create i).comp (annihilate i) = numberOperator i from rfl,
    Common.normalizedWeightedDiagonal_smul,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_numberOperator]
  rw [show Complex.exp ((τ' : ℂ) * (ε i : ℂ)) * Complex.exp (-(τ : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- `G₀,ᵢᵢ(τ, τ)` with the symmetric equal-time convention `θ(0) = 1/2`. -/
theorem freeGibbsGreenFunction_self_time_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) (τ : ℝ) :
    freeGibbsGreenFunction ε β i i τ τ =
      1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) - (2 : ℂ)⁻¹ := by
  rw [freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction,
    weightedFreeTwoPointFunction_self_time,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.exp_add,
    show -(τ : ℂ) * (ε i : ℂ) + (τ : ℂ) * (ε i : ℂ) = 0 by ring,
    show (τ : ℂ) * (ε i : ℂ) + -(τ : ℂ) * (ε i : ℂ) = 0 by ring, Complex.exp_zero, one_smul,
    show (create i).comp (annihilate i) = numberOperator i from rfl]
  rw [neg_smul, Common.normalizedWeightedDiagonal_smul, Common.normalizedWeightedDiagonal_add,
    Common.normalizedWeightedDiagonal_neg, Common.normalizedWeightedDiagonal_smul, one_mul,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_annihilate_comp_create_self,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_numberOperator]
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
    rw [show Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 =
      ((Real.exp (β * ε i) + 1 : ℝ) : ℂ) by push_cast [Complex.ofReal_exp]; ring]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  field_simp
  ring

/-! ## All-index contraction kernels -/

/-- `⟨c_j† c_i⟩₀,β = δᵢⱼ f_i`. -/
theorem freeGibbsDensityOperator_expectation_create_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator ((create j).comp (annihilate i))) =
      if i = j then 1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    change (freeGibbsDensityOperator ε β).expectation
      (Common.finiteHilbertOperator (numberOperator i)) = _
    exact freeGibbsDensityOperator_expectation_numberOperator ε β i
  · rw [if_neg hij, ← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation]
    exact normalizedWeightedDiagonal_create_comp_annihilate_of_ne (freeBoltzmannWeight ε β) hij

/-- `⟨c_i c_j†⟩₀,β = δᵢⱼ (1 - f_i)`. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator ((annihilate i).comp (create j))) =
      if i = j then
        Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact freeGibbsDensityOperator_expectation_annihilate_comp_create_self ε β i
  · rw [if_neg hij, ← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation]
    exact normalizedWeightedDiagonal_annihilate_comp_create_of_ne (freeBoltzmannWeight ε β) hij

/-- `G₀,ᵢⱼ(τ, τ') = 0` for `i ≠ j`, at arbitrary imaginary times. -/
theorem freeGibbsGreenFunction_of_ne (ε : Mode → ℝ) (β : ℝ) {i j : Mode} (hij : i ≠ j)
    (τ τ' : ℝ) : freeGibbsGreenFunction ε β i j τ τ' = 0 := by
  rw [freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction, weightedFreeTwoPointFunction]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [twoPointTimeOrderedProduct_of_gt ε i j h,
      imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Common.normalizedWeightedDiagonal_smul,
      normalizedWeightedDiagonal_annihilate_comp_create_of_ne _ hij]
  · subst h
    rw [twoPointTimeOrderedProduct_self_time ε i j τ',
      imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_add, Common.normalizedWeightedDiagonal_neg,
      normalizedWeightedDiagonal_annihilate_comp_create_of_ne _ hij,
      normalizedWeightedDiagonal_create_comp_annihilate_of_ne _ hij]
  · rw [twoPointTimeOrderedProduct_of_lt ε i j h,
      imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_neg,
      normalizedWeightedDiagonal_create_comp_annihilate_of_ne _ hij]

/-- **Anomalous contractions vanish.** The free Gibbs state is diagonal in the occupation basis, so
the expectation of two annihilation operators is zero: a contraction always pairs a creation
operator with an annihilation operator. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator ((annihilate i).comp (annihilate j))) = 0 := by
  rw [← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    Common.normalizedWeightedDiagonal]
  simp [Common.weightedTrace, matrixCoeff_annihilate_comp_annihilate]

/-- **Anomalous contractions vanish.** The expectation of two creation operators is zero, for the
same particle-number selection rule. -/
theorem freeGibbsDensityOperator_expectation_create_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator ((create i).comp (create j))) = 0 := by
  rw [← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    Common.normalizedWeightedDiagonal]
  simp [Common.weightedTrace, matrixCoeff_create_comp_create]

end Fermionic
end SecondQuantization
