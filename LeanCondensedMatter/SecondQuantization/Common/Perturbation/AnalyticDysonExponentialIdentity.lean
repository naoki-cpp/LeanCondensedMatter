import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Identification of the analytic Dyson evolution with operator exponentials

The Dyson sum and the ordered operator-exponential candidate are identified as the unique solutions
of the same interaction-picture initial-value problem on each compact nonnegative time interval.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The analytic Dyson evolution is continuous on every compact nonnegative time interval. -/
theorem continuousOn_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    ContinuousOn (fun τ => analyticDysonEvolution energy V τ lam) (Icc (0 : ℝ) β) := by
  apply (hasSumUniformlyOn_analyticDysonEvolution energy V hβ lam).tendstoUniformlyOn.continuousOn
  exact Filter.Eventually.of_forall fun s =>
    (continuous_finsetSum s fun n _ => continuous_analyticDysonTerm energy V lam n).continuousOn

/-- The exact operator-exponential candidate is continuous in imaginary time. -/
theorem continuous_analyticDysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    Continuous (fun τ : ℝ => analyticDysonExponentialCandidate energy V τ lam) :=
  continuous_iff_continuousAt.2 fun τ =>
    (hasDerivAt_analyticDysonExponentialCandidate_interactionPicture energy V τ lam).continuousAt

/-- The interaction-picture product with the analytic Dyson evolution is continuous on every
compact nonnegative time interval. -/
theorem continuousOn_interactionPicture_mul_analyticDysonEvolution
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    ContinuousOn (fun τ => continuousInteractionPicture energy V τ *
      analyticDysonEvolution energy V τ lam) (Icc (0 : ℝ) β) := by
  change ContinuousOn (fun τ =>
    (continuousInteractionPicture energy V τ).comp
      (analyticDysonEvolution energy V τ lam)) (Icc (0 : ℝ) β)
  exact (continuous_continuousInteractionPicture energy V).continuousOn.clm_comp
    (continuousOn_analyticDysonEvolution energy V hβ lam)

end
end Common
end SecondQuantization
