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
    𝓢[ℂ, H →L[ℂ] H] :=
  UnitalPositiveLinearMap.ofLinearMap ρ.expectation.toLinearMap
    (fun A hA =>
      ρ.expectation_nonneg_of_isPositive
        (ContinuousLinearMap.nonneg_iff_isPositive.mp hA))
    (by simpa using ρ.expectation_id)

@[simp]
theorem DensityOperator.toState_apply (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.toState A = ρ.expectation A :=
  rfl

end QuantumTheory
