import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteCompletedGibbsCompatibility

set_option linter.style.header false

/-! # Two-point contractions in the finite free-fermion Gibbs state

The thermal state is the explicit-μ Gibbs state on full fermionic occupations.
Every algebraic two-point observable extends to a bounded completed operator;
we transport its finite Gibbs expectation through the generic completed bridge
and use the already-proved completed CAR/KMS contractions.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- `⟨c_i c_j†⟩₀,β = δᵢⱼ (1 - f_i)`. -/
theorem grandCanonicalFiniteGibbsExpectation_annihilate_comp_create
    (ε : Mode → ℝ) (β μ : ℝ) (i j : Mode) :
    Common.finiteGibbsExpectation
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
        ((annihilate i).comp (create j)) =
      if i = j then
        Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1)
      else 0 := by
  have hbridge := Common.finiteGibbsExpectation_eq_completed_of_algebraicCore
    (Config := Occupation Mode)
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ((annihilate i).comp (create j))
      ((completedAnnihilate i).comp (completedCreate j))
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (annihilate i) (create j) (completedAnnihilate i) (completedCreate j)
        (completedAnnihilate_comp_algebraicToCompleted i)
        (completedCreate_comp_algebraicToCompleted j))
  have hpair := hbridge.trans (grandCanonicalGibbsDensityOperator_expectation_pair ε β μ
    (eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (CompletedThermalLadder.annihilate i) (CompletedThermalLadder.create j))
  simp only [CompletedThermalLadder.gibbsFactor_annihilate,
    CompletedThermalLadder.anticommutatorValue] at hpair
  rw [hpair]
  by_cases hij : i = j
  · simp [hij, add_comm]
  · simp [hij]

/-- `⟨c_j† c_i⟩₀,β = δᵢⱼ f_i`. -/
theorem grandCanonicalFiniteGibbsExpectation_create_comp_annihilate
    (ε : Mode → ℝ) (β μ : ℝ) (i j : Mode) :
    Common.finiteGibbsExpectation
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
        ((create j).comp (annihilate i)) =
      if i = j then 1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1) else 0 := by
  have hbridge := Common.finiteGibbsExpectation_eq_completed_of_algebraicCore
    (Config := Occupation Mode)
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ((create j).comp (annihilate i))
      ((completedCreate j).comp (completedAnnihilate i))
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (create j) (annihilate i) (completedCreate j) (completedAnnihilate i)
        (completedCreate_comp_algebraicToCompleted j)
        (completedAnnihilate_comp_algebraicToCompleted i))
  simpa only [] using hbridge.trans
    (grandCanonicalGibbsDensityOperator_expectation_create_comp_annihilate ε β μ
      (eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) i j)

/-- **Anomalous contractions vanish.** The free Gibbs state is diagonal in the occupation basis, so
the expectation of two annihilation operators is zero: a contraction always pairs a creation
operator with an annihilation operator. -/
theorem grandCanonicalFiniteGibbsExpectation_annihilate_comp_annihilate
    (ε : Mode → ℝ) (β μ : ℝ) (i j : Mode) :
    Common.finiteGibbsExpectation
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
        ((annihilate i).comp (annihilate j)) = 0 := by
  have hbridge := Common.finiteGibbsExpectation_eq_completed_of_algebraicCore
    (Config := Occupation Mode)
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ((annihilate i).comp (annihilate j))
      ((completedAnnihilate i).comp (completedAnnihilate j))
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (annihilate i) (annihilate j) (completedAnnihilate i) (completedAnnihilate j)
        (completedAnnihilate_comp_algebraicToCompleted i)
        (completedAnnihilate_comp_algebraicToCompleted j))
  simpa only [CompletedThermalLadder.anticommutatorValue, mul_zero] using
    hbridge.trans (grandCanonicalGibbsDensityOperator_expectation_pair ε β μ
      (eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
      (CompletedThermalLadder.annihilate i) (CompletedThermalLadder.annihilate j))

/-- **Anomalous contractions vanish.** The expectation of two creation operators is zero, for the
same particle-number selection rule. -/
theorem grandCanonicalFiniteGibbsExpectation_create_comp_create
    (ε : Mode → ℝ) (β μ : ℝ) (i j : Mode) :
    Common.finiteGibbsExpectation
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
        ((create i).comp (create j)) = 0 := by
  have hbridge := Common.finiteGibbsExpectation_eq_completed_of_algebraicCore
    (Config := Occupation Mode)
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ((create i).comp (create j))
      ((completedCreate i).comp (completedCreate j))
      (Common.completedProduct_comp_algebraicToCompleted_of_core
        (create i) (create j) (completedCreate i) (completedCreate j)
        (completedCreate_comp_algebraicToCompleted i)
        (completedCreate_comp_algebraicToCompleted j))
  simpa only [CompletedThermalLadder.anticommutatorValue, mul_zero] using
    hbridge.trans (grandCanonicalGibbsDensityOperator_expectation_pair ε β μ
      (eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
      (CompletedThermalLadder.create i) (CompletedThermalLadder.create j))

end Fermionic
end SecondQuantization
