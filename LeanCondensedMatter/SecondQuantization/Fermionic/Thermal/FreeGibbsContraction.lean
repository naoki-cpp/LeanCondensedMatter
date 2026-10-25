import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.FiniteGibbsTraceCompatibility
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

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- `⟨c_i c_j†⟩₀,β = δᵢⱼ (1 - f_i)`. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (create j))) =
      if i = j then
        Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
      else 0 := by
  have hbridge := freeGibbsExpectation_eq_completed_of_algebraicCore
    ε β 0 ((annihilate i).comp (create j))
      ((completedAnnihilate i).comp (completedCreate j))
      (completedNormalProduct_comp_algebraicToCompleted i j)
  simp only [sub_zero] at hbridge
  rw [hbridge, grandCanonicalGibbsDensityOperator_expectation_annihilate_comp_create]
  simp only [sub_zero]
  by_cases hij : i = j
  · simp [hij, add_comm]
  · simp [hij]

/-- `⟨c_j† c_i⟩₀,β = δᵢⱼ f_i`. -/
theorem freeGibbsDensityOperator_expectation_create_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((create j).comp (annihilate i))) =
      if i = j then 1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) else 0 := by
  have hbridge := freeGibbsExpectation_eq_completed_of_algebraicCore
    ε β 0 ((create j).comp (annihilate i))
      ((completedCreate j).comp (completedAnnihilate i))
      (completedReversedNormalProduct_comp_algebraicToCompleted i j)
  simp only [sub_zero] at hbridge
  have hcompleted := grandCanonicalGibbsDensityOperator_expectation_create_comp_annihilate
    ε β 0 (eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0) β) i j
  rw [hbridge, hcompleted]
  simp only [sub_zero]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_one]
    have hne : Complex.exp ((β : ℂ) * (ε i : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    rw [show -(β : ℂ) * (ε i : ℂ) = -((β : ℂ) * (ε i : ℂ)) by ring,
      Complex.exp_neg]
    field_simp
  · simp [hij]

/-- **Anomalous contractions vanish.** The free Gibbs state is diagonal in the occupation basis, so
the expectation of two annihilation operators is zero: a contraction always pairs a creation
operator with an annihilation operator. -/
theorem freeGibbsDensityOperator_expectation_annihilate_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((annihilate i).comp (annihilate j))) = 0 := by
  rw [freeGibbsDensityOperator_expectation_eq_summableDiagonalTraceRatioLinear]
  change Common.tsumTrace ((Common.diagonalEvolution (fermionEnergy ε) (-β)).comp
      ((annihilate i).comp (annihilate j))) /
    Common.tsumTrace (Common.diagonalEvolution (fermionEnergy ε) (-β)) = 0
  simpa only [Common.diagonalEvolution] using
    (Common.diagonalTraceRatio_eq_zero_of_carriesShift
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
  change Common.tsumTrace ((Common.diagonalEvolution (fermionEnergy ε) (-β)).comp
      ((create i).comp (create j))) /
    Common.tsumTrace (Common.diagonalEvolution (fermionEnergy ε) (-β)) = 0
  simpa only [Common.diagonalEvolution] using
    (Common.diagonalTraceRatio_eq_zero_of_carriesShift
      ((carriesParticleNumberCharge_create i).comp
        (carriesParticleNumberCharge_create j))
      (by norm_num)
      (fun n : Occupation Mode =>
        Complex.exp (((-β) * fermionEnergy ε n : ℝ) : ℂ)))

end Fermionic
end SecondQuantization
