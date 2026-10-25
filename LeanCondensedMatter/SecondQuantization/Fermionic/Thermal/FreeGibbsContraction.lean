import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.FiniteGibbsTraceCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import Mathlib.Tactic.FieldSimp

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
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (annihilate i) (create j) (completedAnnihilate i) (completedCreate j)
        (completedAnnihilate_comp_algebraicToCompleted i)
        (completedCreate_comp_algebraicToCompleted j))
  simp only [sub_zero] at hbridge
  have hpair := grandCanonicalGibbsDensityOperator_expectation_pair ε β 0
    (eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0) β)
    (CompletedThermalLadder.annihilate i) (CompletedThermalLadder.create j)
  simp only [CompletedThermalLadder.operator_annihilate,
    CompletedThermalLadder.operator_create,
    CompletedThermalLadder.gibbsFactor_annihilate,
    CompletedThermalLadder.anticommutatorValue] at hpair
  rw [hbridge, hpair]
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
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (create j) (annihilate i) (completedCreate j) (completedAnnihilate i)
        (completedCreate_comp_algebraicToCompleted j)
        (completedAnnihilate_comp_algebraicToCompleted i))
  simp only [sub_zero] at hbridge
  have hpair := grandCanonicalGibbsDensityOperator_expectation_pair ε β 0
    (eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0) β)
    (CompletedThermalLadder.create j) (CompletedThermalLadder.annihilate i)
  simp only [CompletedThermalLadder.operator_create,
    CompletedThermalLadder.operator_annihilate,
    CompletedThermalLadder.gibbsFactor_create,
    CompletedThermalLadder.anticommutatorValue] at hpair
  rw [hbridge, hpair]
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
  have hbridge := freeGibbsExpectation_eq_completed_of_algebraicCore
    ε β 0 ((annihilate i).comp (annihilate j))
      ((completedAnnihilate i).comp (completedAnnihilate j))
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (annihilate i) (annihilate j) (completedAnnihilate i) (completedAnnihilate j)
        (completedAnnihilate_comp_algebraicToCompleted i)
        (completedAnnihilate_comp_algebraicToCompleted j))
  simp only [sub_zero] at hbridge
  rw [hbridge]
  have hpair := grandCanonicalGibbsDensityOperator_expectation_pair ε β 0
    (eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0) β)
    (CompletedThermalLadder.annihilate i) (CompletedThermalLadder.annihilate j)
  simpa only [CompletedThermalLadder.operator_annihilate,
    CompletedThermalLadder.anticommutatorValue, mul_zero] using hpair

/-- **Anomalous contractions vanish.** The expectation of two creation operators is zero, for the
same particle-number selection rule. -/
theorem freeGibbsDensityOperator_expectation_create_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv ((create i).comp (create j))) = 0 := by
  have hbridge := freeGibbsExpectation_eq_completed_of_algebraicCore
    ε β 0 ((create i).comp (create j))
      ((completedCreate i).comp (completedCreate j))
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (create i) (create j) (completedCreate i) (completedCreate j)
        (completedCreate_comp_algebraicToCompleted i)
        (completedCreate_comp_algebraicToCompleted j))
  simp only [sub_zero] at hbridge
  rw [hbridge]
  have hpair := grandCanonicalGibbsDensityOperator_expectation_pair ε β 0
    (eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0) β)
    (CompletedThermalLadder.create i) (CompletedThermalLadder.create j)
  simpa only [CompletedThermalLadder.operator_create,
    CompletedThermalLadder.anticommutatorValue, mul_zero] using hpair

end Fermionic
end SecondQuantization
