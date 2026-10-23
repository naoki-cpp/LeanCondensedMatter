import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Two-point contractions in the finite free-fermion Gibbs state

The state is diagonal in the occupation basis. Mixed contractions give the Fermi-Dirac
occupations; anomalous contractions vanish by particle-number conservation.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- `⟨c_i c_j†⟩₀,β = δᵢⱼ (1 - f_i)`. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (create j))) =
      if i = j then
        Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
      else 0 := by
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  have hC :
      Common.heisenbergEvolve (fermionEnergy ε) (-β) (annihilate i) =
        Complex.exp (((-ε i) * (-β) : ℝ) : ℂ) • annihilate i := by
    simpa [mul_comm] using
      (Common.heisenbergEvolve_eq_smul_of_carriesShift
        (fermionEnergy ε) (-ε i) (-β) (annihilate i)
        (carriesEnergyShift_annihilate ε i))
  have hcomm :
      Common.exchangeCommutator Common.Statistics.fermion (annihilate i) (create j) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion] using
      (anticomm_annihilate_create (Mode := Mode) i j)
  have hne := one_sub_zetaInt_fermion_mul_exp_ne_zero (-ε i) β
  have h := Common.finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator
    (fermionEnergy ε) β (-ε i) Common.Statistics.fermion
    (if i = j then (1 : ℂ) else 0) (annihilate i) (create j) hC hcomm hne
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl] at h ⊢
    rw [h]
    have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    rw [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_one_mul,
      sub_neg_eq_add, show ((-ε i * β : ℝ) : ℂ) = -((β : ℂ) * (ε i : ℂ)) by
        push_cast
        ring, Complex.exp_neg]
    field_simp
  · rw [ite_eq_right hij] at h ⊢
    simpa [hij] using h
/-- `⟨c_j† c_i⟩₀,β = δᵢⱼ f_i`. -/
theorem freeGibbsDensityOperator_expectation_create_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((create j).comp (annihilate i))) =
      if i = j then 1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) else 0 := by
  have hknown := freeGibbsDensityOperator_expectation_annihilate_comp_create ε β i j
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] at hknown ⊢
  simp only [Common.finiteGibbsExpectation] at hknown ⊢
  have h := congrArg (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β)
    (anticomm_annihilate_create (Mode := Mode) i j)
  simp only [ScalarExchange.zetaCommutator, Module.End.mul_eq_comp,
    neg_one_smul, sub_neg_eq_add, map_add] at h
  rcases eq_or_ne i j with rfl | hij
  · simp only [ite_true] at h hknown ⊢
    rw [hknown] at h
    have hid : Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β LinearMap.id = 1 :=
      Common.finiteGibbsExpectation_id (fermionEnergy ε) β
    rw [hid] at h
    have hne : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
      simpa [Common.Statistics.zetaInt_fermion, add_comm] using
        (one_sub_zetaInt_fermion_mul_exp_ne_zero β (ε i))
    field_simp [hne] at h ⊢
    linear_combination h
  · simp only [ite_eq_right hij, map_zero] at h hknown ⊢
    simpa only [hknown, zero_add] using h

/-- **Anomalous contractions vanish.** The free Gibbs state is diagonal in the occupation basis, so
the expectation of two annihilation operators is zero: a contraction always pairs a creation
operator with an annihilation operator. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (annihilate j))) = 0 := by
  rw [freeGibbsDensityOperator_expectation_eq_summableDiagonalTraceRatioLinear]
  simpa only [Common.diagonalEvolution] using
    (Common.summableDiagonalTraceRatioLinear_eq_zero_of_carriesShift
      ((carriesParticleNumberCharge_annihilate i).comp
        (carriesParticleNumberCharge_annihilate j))
      (by norm_num)
      (fun n : Occupation Mode =>
        Complex.exp (((-β) * fermionEnergy ε n : ℝ) : ℂ)))

/-- **Anomalous contractions vanish.** The expectation of two creation operators is zero, for the
same particle-number selection rule. -/
theorem freeGibbsDensityOperator_expectation_create_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((create i).comp (create j))) = 0 := by
  rw [freeGibbsDensityOperator_expectation_eq_summableDiagonalTraceRatioLinear]
  simpa only [Common.diagonalEvolution] using
    (Common.summableDiagonalTraceRatioLinear_eq_zero_of_carriesShift
      ((carriesParticleNumberCharge_create i).comp
        (carriesParticleNumberCharge_create j))
      (by norm_num)
      (fun n : Occupation Mode =>
        Complex.exp (((-β) * fermionEnergy ε n : ℝ) : ℂ)))

end Fermionic
end SecondQuantization
