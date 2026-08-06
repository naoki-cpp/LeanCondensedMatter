import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering

set_option linter.style.header false

/-!
# Closed-form free Gibbs Green function

This module evaluates the finite free-fermion imaginary-time Green function in the occupation basis.
It proves off-diagonal mixed contractions vanish for any diagonal weight, derives the diagonal Gibbs
contractions from the canonical density operator, and gives the one-sided and equal-time closed
forms of `freeGibbsGreenFunction`.

Off-diagonal vanishing is mode-specific rather than a consequence of the `U(1)` particle-number
selection rule: the mixed operators have zero total charge, but toggling distinct modes cannot
return an occupation basis state to itself. At equal times, the `θ(0) = 1/2` convention in
`timeOrderedProduct` gives a value distinct from both one-sided limits.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Off-diagonal (`i ≠ j`): both mixed contractions vanish identically, for any weight -/

omit [Fintype Mode] in
/-- **`⟨n| c_i c_j† |n⟩ = 0` for `i ≠ j`.** Acting with `create j` then `annihilate i` on
`basisState n` either vanishes outright, or lands on a basis state that differs from `n` at mode
`i` (removed by `annihilate i`, and never reintroduced since `i ≠ j`) — so it can never return a
nonzero `n`-coefficient. -/
theorem matrixCoeff_annihilate_comp_create_of_ne {i j : Mode} (hij : i ≠ j)
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
/-- **`⟨n| c_j† c_i |n⟩ = 0` for `i ≠ j`**, the mirror of
`matrixCoeff_annihilate_comp_create_of_ne`, via CAR's `{c_i, c_j†} = 0`
(`anticomm_annihilate_create`) at `i ≠ j`: the two orders sum to zero, so one vanishing forces the
other. -/
theorem matrixCoeff_create_comp_annihilate_of_ne {i j : Mode} (hij : i ≠ j)
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

theorem weightedTrace_annihilate_comp_create_of_ne (w : Occupation Mode → ℂ) {i j : Mode}
    (hij : i ≠ j) : Common.weightedTrace w ((annihilate i).comp (create j)) = 0 := by
  simp [Common.weightedTrace, matrixCoeff_annihilate_comp_create_of_ne hij]

theorem weightedTrace_create_comp_annihilate_of_ne (w : Occupation Mode → ℂ) {i j : Mode}
    (hij : i ≠ j) : Common.weightedTrace w ((create j).comp (annihilate i)) = 0 := by
  simp [Common.weightedTrace, matrixCoeff_create_comp_annihilate_of_ne hij]

theorem normalizedWeightedDiagonal_annihilate_comp_create_of_ne (w : Occupation Mode → ℂ)
    {i j : Mode} (hij : i ≠ j) :
    Common.normalizedWeightedDiagonal w ((annihilate i).comp (create j)) = 0 := by
  rw [Common.normalizedWeightedDiagonal, weightedTrace_annihilate_comp_create_of_ne w hij, zero_div]

theorem normalizedWeightedDiagonal_create_comp_annihilate_of_ne (w : Occupation Mode → ℂ)
    {i j : Mode} (hij : i ≠ j) :
    Common.normalizedWeightedDiagonal w ((create j).comp (annihilate i)) = 0 := by
  rw [Common.normalizedWeightedDiagonal, weightedTrace_create_comp_annihilate_of_ne w hij, zero_div]

omit [LinearOrder Mode] in
private theorem normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation
    (ε : Mode → ℝ) (β : ℝ) (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β) A =
      (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperator A) := by
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β :=
    funext (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β)
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_eq_normalizedWeightedDiagonal, hw]

/-! ## Diagonal (`i = j`): the free hole/occupation numbers `1 - f_i`, `f_i` -/

/-- **The free hole number** `⟨c_i c_i†⟩₀,β = 1 - ⟨N_i⟩₀,β = e^{βε_i}/(e^{βε_i}+1)`. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_create_self
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

/-! ## The closed-form free thermal Green function -/

/-- **`G₀,ᵢᵢ(τ, τ')` for `τ' < τ`**: `-e^{-(τ-τ')ε_i} · e^{βε_i}/(e^{βε_i}+1)`. -/
theorem freeGibbsGreenFunction_of_gt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ' < τ) :
    freeGibbsGreenFunction ε β i i τ τ' =
      - (Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1))) := by
  rw [freeGibbsGreenFunction, weightedFreeTwoPointFunction_of_gt ε (freeBoltzmannWeight ε β) i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul, Common.normalizedWeightedDiagonal_smul,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_annihilate_comp_create_self]
  rw [show Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * Complex.exp ((τ' : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- **`G₀,ᵢᵢ(τ, τ')` for `τ < τ'`**: `e^{-(τ-τ')ε_i} · 1/(e^{βε_i}+1)`. -/
theorem freeGibbsGreenFunction_of_lt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ < τ') :
    freeGibbsGreenFunction ε β i i τ τ' =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)) := by
  rw [freeGibbsGreenFunction, weightedFreeTwoPointFunction_of_lt ε (freeBoltzmannWeight ε β) i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    show (create i).comp (annihilate i) = numberOperator i from rfl,
    Common.normalizedWeightedDiagonal_smul,
    normalizedWeightedDiagonal_freeBoltzmannWeight_eq_expectation,
    freeGibbsDensityOperator_expectation_numberOperator]
  rw [show Complex.exp ((τ' : ℂ) * (ε i : ℂ)) * Complex.exp (-(τ : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- **`G₀,ᵢᵢ(τ, τ)`, the equal-time, same-mode case**, `f_i - 1/2`. Not a limit of either one-sided
formula above: `timeOrderedProduct`'s `θ(0) = 1/2` convention symmetrizes
`½(⟨c_i(τ) c_i†(τ)⟩ - ⟨c_i†(τ) c_i(τ)⟩) = ½((1-f_i) - f_i) = 1/2 - f_i`, giving `G₀,ᵢᵢ(τ,τ) =
-(1/2 - f_i) = f_i - 1/2` — genuinely discontinuous against both one-sided limits `G₀,ᵢᵢ(τ,τ'⁺) →
-(1-f_i)` and `G₀,ᵢᵢ(τ,τ'⁻) → f_i` as `τ' → τ` (their difference is `-1`, forced by CAR, matching
`weightedFreeTwoPointFunction_self_time`'s module-level remark). -/
theorem freeGibbsGreenFunction_self_time_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) (τ : ℝ) :
    freeGibbsGreenFunction ε β i i τ τ =
      1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) - (2 : ℂ)⁻¹ := by
  rw [freeGibbsGreenFunction, weightedFreeTwoPointFunction_self_time,
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

/-! ## All-index (`if i = j then ... else 0`) forms, for Wick's theorem's contraction kernel -/

/-- **`⟨c_j† c_i⟩₀,β`, all indices**: `δᵢⱼ · f_i`, `0` off-diagonal. Combines
`freeGibbsDensityOperator_expectation_numberOperator` (`i = j`) with the off-diagonal coordinate
calculation, which holds for any weight and hence specializes directly to `freeBoltzmannWeight`. -/
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

/-- **`⟨c_i c_j†⟩₀,β`, all indices**: `δᵢⱼ · (1 - f_i)`, `0` off-diagonal. The mirror
of `freeGibbsDensityOperator_expectation_create_comp_annihilate`. -/
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

/-- **`G₀,ᵢⱼ(τ, τ') = 0` for `i ≠ j`**, at any `τ, τ'` (both time-ordering branches vanish
identically, from `normalizedWeightedDiagonal_annihilate_comp_create_of_ne`/
`_create_comp_annihilate_of_ne`). -/
theorem freeGibbsGreenFunction_of_ne (ε : Mode → ℝ) (β : ℝ) {i j : Mode} (hij : i ≠ j)
    (τ τ' : ℝ) : freeGibbsGreenFunction ε β i j τ τ' = 0 := by
  rw [freeGibbsGreenFunction, weightedFreeTwoPointFunction]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [Common.timeOrderedProduct_of_gt Common.Statistics.fermion _ _ h, imaginaryTimeEvolve_annihilate,
      imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Common.normalizedWeightedDiagonal_smul,
      normalizedWeightedDiagonal_annihilate_comp_create_of_ne _ hij]
  · subst h
    rw [Common.timeOrderedProduct_self_time Common.Statistics.fermion, imaginaryTimeEvolve_annihilate,
      imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_add, Common.normalizedWeightedDiagonal_neg,
      normalizedWeightedDiagonal_annihilate_comp_create_of_ne _ hij,
      normalizedWeightedDiagonal_create_comp_annihilate_of_ne _ hij]
  · rw [Common.timeOrderedProduct_of_lt Common.Statistics.fermion _ _ h, imaginaryTimeEvolve_annihilate,
      imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Common.normalizedWeightedDiagonal_smul,
      Common.normalizedWeightedDiagonal_neg,
      normalizedWeightedDiagonal_create_comp_annihilate_of_ne _ hij]

end Fermionic
end SecondQuantization
