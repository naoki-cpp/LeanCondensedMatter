import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDysonBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-!
# Convergent analytic Dyson evolution

This module sums the finite-dimensional continuous Dyson coefficients in operator norm.  The
coefficient recursion remains the transported algebraic construction from `ContinuousDyson`; the
new definition is the genuine `tsum` of those coefficients.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The `n`th perturbatively weighted continuous Dyson coefficient. -/
noncomputable def analyticDysonTerm (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) (n : ℕ) : FiniteContinuousOperator Config :=
  lam ^ n • continuousDysonCoeff energy V n τ

/-- The norm-convergent interaction-picture Dyson evolution. -/
noncomputable def analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) : FiniteContinuousOperator Config :=
  ∑' n : ℕ, analyticDysonTerm energy V τ lam n

/-- On every nonnegative compact imaginary-time interval, the analytic Dyson terms are summable
in the continuous-operator norm. -/
theorem summable_analyticDysonTerm (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    Summable (analyticDysonTerm energy V τ lam) := by
  exact (summable_norm_pow_smul_continuousDysonCoeff energy V hβ hτ lam).of_norm

/-- The defining operator series has sum `analyticDysonEvolution`. -/
theorem hasSum_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (analyticDysonTerm energy V τ lam)
      (analyticDysonEvolution energy V τ lam) := by
  exact (summable_analyticDysonTerm energy V hβ hτ lam).hasSum

/-- At zero imaginary time only the zeroth Dyson coefficient survives. -/
@[simp]
theorem analyticDysonEvolution_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    analyticDysonEvolution energy V 0 lam = 1 := by
  rw [analyticDysonEvolution, tsum_eq_single 0]
  · simp [analyticDysonTerm]
  · intro n hn
    simp [analyticDysonTerm, continuousDysonCoeff_at_zero, hn]

end
end Common
end SecondQuantization
