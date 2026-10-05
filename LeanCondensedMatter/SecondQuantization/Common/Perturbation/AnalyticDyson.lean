import LeanCondensedMatter.Analysis.Dyson.Bounds
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson

set_option linter.style.header false

/-!
# Convergent analytic Dyson evolution

The finite continuous operators remain the public realization, while their recursion and
convergence are inherited from the dimension-independent `Analysis.Dyson` owner.
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

/-- The defining operator series has sum `analyticDysonEvolution`. -/
theorem hasSum_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (analyticDysonTerm energy V τ lam)
      (analyticDysonEvolution energy V τ lam) := by
  obtain ⟨M, hBound⟩ := Dyson.exists_continuousBoundedInteraction
    (continuousInteractionPicture energy V) hβ
    (continuous_continuousInteractionPicture energy V)
    ContinuousLinearMap.norm_id_le
  have hterm : analyticDysonTerm energy V τ lam =
      Dyson.term (continuousInteractionPicture energy V) lam τ := by
    funext n
    exact analyticDysonTerm_eq_term energy V τ lam n
  rw [hterm, analyticDysonEvolution_eq_evolution]
  exact Dyson.hasSum_evolution_of_bound hBound.toBoundedInteraction lam hτ

end
end Common
end SecondQuantization
