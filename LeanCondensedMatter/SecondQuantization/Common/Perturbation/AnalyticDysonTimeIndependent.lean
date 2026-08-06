import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponentialUniqueness
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansionVerification

set_option linter.style.header false

/-!
# Time-independent analytic Dyson evolution

When the interaction-picture operator is constant, every Dyson term reduces to the corresponding
ordinary exponential-series coefficient. Consequently, the norm-convergent analytic Dyson
evolution is exactly the operator exponential of `-τ λ V`.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- In the time-independent case, each weighted continuous Dyson term is the corresponding
ordinary exponential-series coefficient. -/
theorem analyticDysonTerm_eq_of_time_independent (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hV : ∀ τ, interactionPicture energy V τ = V)
    (τ : ℝ) (lam : ℂ) (n : ℕ) :
    analyticDysonTerm energy V τ lam n =
      ((((-τ : ℂ) * lam) ^ n) / n.factorial) •
        (finiteContinuousOperator V) ^ n := by
  rw [analyticDysonTerm, continuousDysonCoeff,
    dysonCoeff_eq_of_time_independent energy V hV n τ,
    finiteContinuousOperator_smul, finiteContinuousOperator_pow, smul_smul]
  congr 1
  ring

/-- If the interaction picture is time-independent, the analytic Dyson sum is the ordinary
operator exponential of `-τ λ V`. -/
theorem analyticDysonEvolution_eq_exp_of_time_independent (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hV : ∀ τ, interactionPicture energy V τ = V)
    {τ : ℝ} (hτ : 0 ≤ τ) (lam : ℂ) :
    analyticDysonEvolution energy V τ lam =
      NormedSpace.exp (((-τ : ℂ) * lam) • finiteContinuousOperator V) := by
  have hDyson := hasSum_analyticDysonEvolution
    (β := τ) (τ := τ) energy V hτ ⟨hτ, le_rfl⟩ lam
  have hExp := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (((-τ : ℂ) * lam) • finiteContinuousOperator V)
  have hterms :
      (fun n : ℕ => analyticDysonTerm energy V τ lam n) =
      (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) •
        ((((-τ : ℂ) * lam) • finiteContinuousOperator V) ^ n)) := by
    funext n
    rw [analyticDysonTerm_eq_of_time_independent energy V hV τ lam n]
    simp only [smul_pow, smul_smul]
    congr 1
    field_simp
  have hDyson' : HasSum
      (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) •
        ((((-τ : ℂ) * lam) • finiteContinuousOperator V) ^ n))
      (analyticDysonEvolution energy V τ lam) := by
    rw [← hterms]
    exact hDyson
  exact hDyson'.unique hExp

end
end Common
end SecondQuantization
