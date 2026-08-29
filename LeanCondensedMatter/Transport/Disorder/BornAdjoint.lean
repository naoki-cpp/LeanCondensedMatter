import LeanCondensedMatter.Transport.Disorder.RetardedBorn
import LeanCondensedMatter.Transport.Disorder.AdvancedBorn

set_option linter.style.header false

/-!
# Retarded/advanced Born adjoint bridge

This module sits downstream of the retarded and advanced first-Born sibling modules and records the
adjoint equivalences between their orientation-sensitive exact remainders and closure data. The
siblings remain independent and do not import one another.

No new Born approximation, closure assumption, self-consistency, or exact-average identification is
introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The conventional advanced Born self-energy is the adjoint of the conventional retarded one. -/
theorem star_bornRetardedSelfEnergy
    (energy broadening : ℝ) :
    star (ensemble.bornRetardedSelfEnergy energy broadening) =
      ensemble.bornAdvancedSelfEnergy energy broadening := by
  rw [← ensemble.bornSelfEnergy_retarded, ← ensemble.bornSelfEnergy_advanced]
  exact ensemble.star_bornSelfEnergy_retarded energy broadening

/-- The exact advanced second-order Dyson remainder is the adjoint of the exact retarded remainder.
The reversal of operator order under adjunction is exactly the advanced orientation. -/
theorem star_exactSecondOrderRetardedRemainder
    (energy broadening : ℝ) :
    star (ensemble.exactSecondOrderRetardedRemainder energy broadening) =
      ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
  unfold exactSecondOrderRetardedRemainder exactSecondOrderAdvancedRemainder
  rw [← ensemble.operatorAverage_star]
  apply congrArg ensemble.operatorAverage
  funext ω
  simp [star_mul, ensemble.star_configurationRetardedGreen,
    ensemble.star_freeRetardedGreen, (ensemble.impurityPotential ω).2.star_eq, mul_assoc]

/-- The advanced exact Born closure error is the adjoint of the retarded closure error. -/
theorem star_bornRetardedClosureError
    (energy broadening : ℝ) :
    star (ensemble.bornRetardedClosureError energy broadening) =
      ensemble.bornAdvancedClosureError energy broadening := by
  unfold bornRetardedClosureError bornAdvancedClosureError
  rw [star_secondOrderBornClosureError]
  rw [ensemble.star_freeRetardedGreen]
  rw [ensemble.star_exactSecondOrderRetardedRemainder]
  rw [ensemble.star_bornRetardedSelfEnergy]

/-- Retarded and advanced Born closure hypotheses are equivalent; they are not independent physical
assumptions once the exact R/A adjoint structure is fixed. -/
theorem retardedBornClosureHypothesis_iff_advanced
    (energy broadening : ℝ) :
    RetardedBornClosureHypothesis ensemble energy broadening ↔
      AdvancedBornClosureHypothesis ensemble energy broadening := by
  constructor
  · intro hretarded
    refine ⟨?_⟩
    have hstar := congrArg star hretarded.closureError_eq_zero
    simpa [ensemble.star_bornRetardedClosureError] using hstar
  · intro hadvanced
    refine ⟨?_⟩
    have hstar :
        star (ensemble.bornRetardedClosureError energy broadening) = 0 := by
      rw [ensemble.star_bornRetardedClosureError]
      exact hadvanced.closureError_eq_zero
    have hback := congrArg star hstar
    simpa using hback

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
