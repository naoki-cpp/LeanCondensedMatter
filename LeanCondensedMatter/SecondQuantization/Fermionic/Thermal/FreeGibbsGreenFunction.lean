import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# Closed-form free Gibbs Green function

This module defines the finite free-fermion imaginary-time Green function directly from the
canonical Gibbs density operator. Coordinate lemmas for off-diagonal mixed contractions remain
private proof infrastructure. Arbitrary weighted two-point functionals are kept private here as
coordinate lemmas rather than exported as a competing thermal-state API.

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

/-! ## Private weighted-coordinate helpers -/

private noncomputable def weightedFreeTwoPointFunction (ε : Mode → ℝ)
    (w : Occupation Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - Common.normalizedWeightedDiagonal w (twoPointTimeOrderedProduct ε i j τ τ')

private theorem weightedFreeTwoPointFunction_of_gt (ε : Mode → ℝ)
    (w : Occupation Mode → ℂ) (i j : Mode) {τ τ' : ℝ} (h : τ' < τ) :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      - Common.normalizedWeightedDiagonal w
          ((imaginaryTimeEvolve ε τ (annihilate i)).comp
            (imaginaryTimeEvolve ε τ' (create j))) := by
  rw [weightedFreeTwoPointFunction, twoPointTimeOrderedProduct_of_gt ε i j h]

private theorem weightedFreeTwoPointFunction_of_lt (ε : Mode → ℝ)
    (w : Occupation Mode → ℂ) (i j : Mode) {τ τ' : ℝ} (h : τ < τ') :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      Common.normalizedWeightedDiagonal w
        ((imaginaryTimeEvolve ε τ' (create j)).comp
          (imaginaryTimeEvolve ε τ (annihilate i))) := by
  rw [weightedFreeTwoPointFunction, twoPointTimeOrderedProduct_of_lt ε i j h,
    Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_one_smul,
    (Common.normalizedWeightedDiagonal w).map_neg, neg_neg]

private theorem weightedFreeTwoPointFunction_self_time (ε : Mode → ℝ)
    (w : Occupation Mode → ℂ) (i j : Mode) (τ : ℝ) :
    weightedFreeTwoPointFunction ε w i j τ τ =
      - Common.normalizedWeightedDiagonal w
          ((2⁻¹ : ℂ) • ((imaginaryTimeEvolve ε τ (annihilate i)).comp
              (imaginaryTimeEvolve ε τ (create j)) +
            (-1 : ℂ) •
              ((imaginaryTimeEvolve ε τ (create j)).comp
                (imaginaryTimeEvolve ε τ (annihilate i))))) := by
  rw [weightedFreeTwoPointFunction, twoPointTimeOrderedProduct_self_time,
    Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]

/-- The physical free Gibbs Green function
`G₀,ᵢⱼ(τ, τ') = -Tr(ρ₀,β Tτ cᵢ(τ)cⱼ†(τ'))`. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - (freeGibbsDensityOperator ε β).expectation
      (Common.finiteHilbertOperatorAlgEquiv (twoPointTimeOrderedProduct ε i j τ τ'))

/-! ## Gibbs-state bridge and BDD mixed contractions -/

omit [LinearOrder Mode] in
private theorem normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation
    (ε : Mode → ℝ) (β : ℝ) (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β) A =
      (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperatorAlgEquiv A) := by
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β :=
    funext (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β)
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_eq_normalizedWeightedDiagonal, hw]

/-- The density-state Green function agrees with its private finite occupation-coordinate evaluation. -/
private theorem freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ) :
    freeGibbsGreenFunction ε β i j τ τ' =
      weightedFreeTwoPointFunction ε (freeBoltzmannWeight ε β) i j τ τ' := by
  rw [freeGibbsGreenFunction, weightedFreeTwoPointFunction,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation]

private theorem freeGibbsDensityOperator_expectation_annihilate_comp_create_bdd
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (create j))) =
      if i = j then
        Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, ← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
      annihilate_comp_create_self,
      (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_sub,
      Common.normalizedWeightedDiagonal_id _ (weightSum_freeBoltzmannWeight_ne_zero ε β),
      normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
      freeGibbsDensityOperator_expectation_numberOperator]
    have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
      simpa [Common.Statistics.zetaInt_fermion, add_comm] using
        (one_sub_zetaInt_fermion_mul_exp_ne_zero β (ε i))
    field_simp
    ring
  · rw [if_neg hij, freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
    have hC :
        Common.heisenbergEvolve (fermionEnergy ε) (-β) (annihilate i) =
          Complex.exp (((-ε i) * (-β) : ℝ) : ℂ) • annihilate i := by
      simpa [mul_comm] using
        (Common.heisenbergEvolve_eq_smul_of_carriesShift
          (fermionEnergy ε) (-ε i) (-β) (annihilate i)
          (carriesEnergyShift_annihilate ε i))
    have hcomm :
        Common.exchangeCommutator Common.Statistics.fermion (annihilate i) (create j) =
          (0 : ℂ) • (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
      simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion, hij] using
        (anticomm_annihilate_create (Mode := Mode) i j)
    have hne := one_sub_zetaInt_fermion_mul_exp_ne_zero (-ε i) β
    simpa using
      (Common.finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator
        (fermionEnergy ε) β (-ε i) Common.Statistics.fermion 0
        (annihilate i) (create j) hC hcomm hne)

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
    LinearMap.comp_smul, smul_smul,
    (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_smul, smul_eq_mul,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_annihilate_comp_create_bdd, if_pos rfl]
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
    (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_smul, smul_eq_mul,
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
  rw [neg_smul,
    (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_smul,
    (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_add,
    (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_neg,
    (Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)).map_smul,
    smul_eq_mul, one_smul ℂ,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_annihilate_comp_create_bdd,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_numberOperator]
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
    simpa [Common.Statistics.zetaInt_fermion, add_comm] using
      (one_sub_zetaInt_fermion_mul_exp_ne_zero β (ε i))
  rw [if_pos rfl]
  field_simp
  ring

/-! ## All-index contraction kernels -/

/-- `⟨c_j† c_i⟩₀,β = δᵢⱼ f_i`. -/
theorem freeGibbsDensityOperator_expectation_create_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((create j).comp (annihilate i))) =
      if i = j then 1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) else 0 := by
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  have hC :
      Common.heisenbergEvolve (fermionEnergy ε) (-β) (create j) =
        Complex.exp (((ε j) * (-β) : ℝ) : ℂ) • create j := by
    simpa [mul_comm] using
      (Common.heisenbergEvolve_eq_smul_of_carriesShift
        (fermionEnergy ε) (ε j) (-β) (create j) (carriesEnergyShift_create ε j))
  have hcomm :
      Common.exchangeCommutator Common.Statistics.fermion (create j) (annihilate i) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion, eq_comm] using
      (anticomm_create_annihilate (Mode := Mode) j i)
  have hne := one_sub_zetaInt_fermion_mul_exp_ne_zero (ε j) β
  have h := Common.finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator
    (fermionEnergy ε) β (ε j) Common.Statistics.fermion
    (if i = j then (1 : ℂ) else 0) (create j) (annihilate i) hC hcomm hne
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl] at h ⊢
    simpa [Common.Statistics.zetaInt_fermion, mul_comm, add_comm] using h
  · rw [if_neg hij] at h ⊢
    simpa [hij] using h

/-- `⟨c_i c_j†⟩₀,β = δᵢⱼ (1 - f_i)`. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (create j))) =
      if i = j then
        Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
      else 0 :=
  freeGibbsDensityOperator_expectation_annihilate_comp_create_bdd ε β i j

/-- `G₀,ᵢⱼ(τ, τ') = 0` for `i ≠ j`, at arbitrary imaginary times. -/
theorem freeGibbsGreenFunction_of_ne (ε : Mode → ℝ) (β : ℝ) {i j : Mode} (hij : i ≠ j)
    (τ τ' : ℝ) : freeGibbsGreenFunction ε β i j τ τ' = 0 := by
  rw [freeGibbsGreenFunction_eq_weightedFreeTwoPointFunction, weightedFreeTwoPointFunction]
  simp only [neg_eq_zero]
  unfold twoPointTimeOrderedProduct
  rw [imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
  apply Common.normalizedWeightedDiagonal_timeOrderedProduct_eq_zero
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
      map_smul]
    rw [map_smul, freeGibbsDensityOperator_expectation_annihilate_comp_create, if_neg hij,
      smul_zero]
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
      map_smul]
    rw [map_smul, freeGibbsDensityOperator_expectation_create_comp_annihilate, if_neg hij,
      smul_zero]

/-- **Anomalous contractions vanish.** The free Gibbs state is diagonal in the occupation basis, so
the expectation of two annihilation operators is zero: a contraction always pairs a creation
operator with an annihilation operator. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (annihilate j))) = 0 := by
  rw [← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation]
  exact Common.normalizedWeightedDiagonal_eq_zero_of_matrixCoeff_self_eq_zero _ _
    (matrixCoeff_annihilate_comp_annihilate i j)

/-- **Anomalous contractions vanish.** The expectation of two creation operators is zero, for the
same particle-number selection rule. -/
theorem freeGibbsDensityOperator_expectation_create_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((create i).comp (create j))) = 0 := by
  rw [← normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation]
  exact Common.normalizedWeightedDiagonal_eq_zero_of_matrixCoeff_self_eq_zero _ _
    (matrixCoeff_create_comp_create i j)

end Fermionic
end SecondQuantization
