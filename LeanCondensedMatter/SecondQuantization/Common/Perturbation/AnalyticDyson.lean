import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDysonBounds

set_option linter.style.header false

/-!
# Convergent analytic Dyson evolution

The finite continuous operators remain the public realization, while their recursion, factorial
bounds, summability, and uniform convergence are inherited from the dimension-independent
`Analysis.Dyson` owner.
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

/-- The finite weighted coefficient is the generic Dyson term specialized to the continuous
interaction-picture family. -/
@[simp]
theorem analyticDysonTerm_eq_term (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) (n : ℕ) :
    analyticDysonTerm energy V τ lam n =
      Dyson.term (continuousInteractionPicture energy V) lam τ n := by
  rw [analyticDysonTerm, Dyson.term, continuousDysonCoeff_eq_coeff]

/-- The finite analytic evolution is the generic Dyson evolution specialized to the continuous
interaction-picture family. -/
theorem analyticDysonEvolution_eq_evolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) :
    analyticDysonEvolution energy V τ lam =
      Dyson.evolution (continuousInteractionPicture energy V) lam τ := by
  rw [analyticDysonEvolution, Dyson.evolution]
  apply tsum_congr
  intro n
  exact analyticDysonTerm_eq_term energy V τ lam n

/-- The weighted `n`th coefficient is controlled by the generic exponential majorant. -/
theorem norm_analyticDysonTerm_le (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) (n : ℕ) :
    ‖analyticDysonTerm energy V τ lam n‖ ≤
      Dyson.majorant
        (‖lam‖ * interactionPictureNormBound energy V β) τ n := by
  rw [analyticDysonTerm_eq_term]
  exact Dyson.norm_term_le_of_bound
    (continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
    (interactionPictureNormBound_nonneg energy V hβ)
    (fun σ hσ => norm_continuousInteractionPicture_le energy V hβ hσ)
    lam n hτ

/-- On every nonnegative compact imaginary-time interval, the analytic Dyson terms are summable
in the continuous-operator norm. -/
theorem summable_analyticDysonTerm (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    Summable (analyticDysonTerm energy V τ lam) := by
  exact (Dyson.summable_term_of_bound
    (continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
    (interactionPictureNormBound_nonneg energy V hβ)
    (fun σ hσ => norm_continuousInteractionPicture_le energy V hβ hσ)
    lam hτ).congr fun n => (analyticDysonTerm_eq_term energy V τ lam n).symm

/-- The defining operator series has sum `analyticDysonEvolution`. -/
theorem hasSum_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (analyticDysonTerm energy V τ lam)
      (analyticDysonEvolution energy V τ lam) := by
  rw [analyticDysonEvolution_eq_evolution]
  exact (Dyson.hasSum_evolution_of_bound
    (continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
    (interactionPictureNormBound_nonneg energy V hβ)
    (fun σ hσ => norm_continuousInteractionPicture_le energy V hβ hσ)
    lam hτ).congr fun n => (analyticDysonTerm_eq_term energy V τ lam n).symm

/-- The analytic Dyson series converges uniformly in operator norm on every compact interval
`[0, β]`. -/
theorem hasSumUniformlyOn_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    HasSumUniformlyOn
      (fun n τ => analyticDysonTerm energy V τ lam n)
      (fun τ => analyticDysonEvolution energy V τ lam)
      (Set.Icc (0 : ℝ) β) := by
  simpa only [analyticDysonTerm_eq_term, analyticDysonEvolution_eq_evolution] using
    (Dyson.hasSumUniformlyOn_evolution_of_bound
      (continuousInteractionPicture energy V)
      ContinuousLinearMap.norm_id_le
      (interactionPictureNormBound_nonneg energy V hβ)
      (fun σ hσ => norm_continuousInteractionPicture_le energy V hβ hσ)
      lam)

/-- At zero imaginary time only the zeroth Dyson coefficient survives. -/
@[simp]
theorem analyticDysonEvolution_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    analyticDysonEvolution energy V 0 lam = 1 := by
  rw [analyticDysonEvolution_eq_evolution]
  exact Dyson.evolution_zero (continuousInteractionPicture energy V) lam

end
end Common
end SecondQuantization
