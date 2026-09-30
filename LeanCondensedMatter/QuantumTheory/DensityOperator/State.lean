import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Observable

set_option linter.style.header false

/-!
# Density operators as probabilistic-theory states

A density operator's normalized positive expectation functional is bundled as PhyslibAlpha's
general state type. This bridge lets measurement and statistical APIs consume density states
without depending on the spectral representation used to construct the expectation.
-/

noncomputable section

namespace QuantumTheory

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density operator as a normalized positive state on the bounded-operator algebra. -/
noncomputable def DensityOperator.toState (ρ : DensityOperator H) :
    𝓢[ℂ, H →L[ℂ] H] where
  toPositiveLinearMap :=
    PositiveLinearMap.mk₀ ρ.expectation.toLinearMap fun A hA =>
      ρ.expectation_nonneg_of_isPositive
        (ContinuousLinearMap.nonneg_iff_isPositive.mp hA)
  map_one' := by
    simpa using ρ.expectation_id

@[simp]
theorem DensityOperator.toState_apply (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.toState A = ρ.expectation A :=
  rfl

/-- Restricting the density state to observables recovers the complex density expectation exactly
after embedding the real observable value into `ℂ`. -/
@[simp]
theorem DensityOperator.coe_toState_onObservables_apply
    (ρ : DensityOperator H) (A : Observable H) :
    ((ρ.toState.onObservables A : ℝ) : ℂ) = ρ.expectation A.1 := by
  simpa using
    (UnitalPositiveLinearMap.coe_onObservables_apply (ω := ρ.toState) (a := A))

end QuantumTheory
