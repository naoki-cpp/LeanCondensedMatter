import LeanCondensedMatter.Analysis.Dyson.Volterra
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDyson

set_option linter.style.header false

/-!
# Finite specialization of the generic Dyson–Volterra equation

The series–integral exchange, tail summation, and Volterra equation are owned by
`Analysis.Dyson.Volterra`. This module retains only the finite continuous-operator specialization
needed by downstream SecondQuantization results.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- Every finite weighted Dyson coefficient is continuous in imaginary time, by specialization of
the generic continuity theorem. -/
theorem continuous_analyticDysonTerm (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (lam : ℂ) (n : ℕ) :
    Continuous (fun τ => analyticDysonTerm energy V τ lam n) := by
  exact (Dyson.continuous_term
    (continuous_continuousInteractionPicture energy V) lam n).congr
      (fun τ => (analyticDysonTerm_eq_term energy V τ lam n).symm)

/-- The finite analytic Dyson evolution solves the Volterra equation by specialization of the
generic bounded-algebra theorem. -/
theorem analyticDysonEvolution_eq_one_sub_integral (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    analyticDysonEvolution energy V τ lam =
      1 - lam • ∫ σ in (0 : ℝ)..τ,
        (continuousInteractionPicture energy V σ).comp
          (analyticDysonEvolution energy V σ lam) := by
  change analyticDysonEvolution energy V τ lam =
    1 - lam • ∫ σ in (0 : ℝ)..τ,
      continuousInteractionPicture energy V σ * analyticDysonEvolution energy V σ lam
  simpa only [analyticDysonEvolution_eq_evolution] using
    (Dyson.evolution_eq_one_sub_integral_of_bound
      (continuous_continuousInteractionPicture energy V)
      ContinuousLinearMap.norm_id_le
      (interactionPictureNormBound_nonneg energy V hβ)
      (fun σ hσ => norm_continuousInteractionPicture_le energy V hβ hσ)
      hτ lam)

end
end Common
end SecondQuantization
