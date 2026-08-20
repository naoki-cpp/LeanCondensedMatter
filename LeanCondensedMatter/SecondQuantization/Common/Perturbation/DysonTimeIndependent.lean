import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponentialUniqueness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# Time-independent Dyson evolution

When the interaction-picture operator is constant, the algebraic Dyson coefficients reduce to
ordinary exponential-series coefficients. The same specialization identifies each weighted analytic
Dyson term and the norm-convergent analytic Dyson evolution with the corresponding operator
exponential.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

omit [Fintype Config] in
/-- In the time-independent case, each algebraic Dyson coefficient is the corresponding ordinary
exponential-series coefficient. -/
theorem dysonCoeff_eq_of_time_independent [Finite Config] (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hV : ∀ τ, interactionPicture energy V τ = V) : ∀ (n : ℕ) (τ : ℝ),
    dysonCoeff energy V n τ = ((-τ : ℂ) ^ n / n.factorial) • V ^ n := by
  letI := Fintype.ofFinite Config
  intro n
  induction n with
  | zero => intro τ; simp [dysonCoeff_zero, Module.End.one_eq_id]
  | succ k ih =>
    intro τ
    rw [dysonCoeff_succ]
    have hcomp : V.comp (V ^ k) = V ^ (k + 1) := by
      rw [pow_succ', Module.End.mul_eq_comp]
    have hfun : (fun σ : ℝ => (interactionPicture energy V σ).comp
        (dysonCoeff energy V k σ)) = fun σ : ℝ =>
          (((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1) := by
      funext σ
      rw [hV σ, ih σ, LinearMap.comp_smul, hcomp]
    rw [hfun]
    have hval : operatorIntervalIntegral
        (fun σ : ℝ => (((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1)) 0 τ =
        (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1) := by
      apply matrixCoeff_ext
      intro m n'
      rw [matrixCoeff_operatorIntervalIntegral]
      simp only [matrixCoeff_smul]
      rw [intervalIntegral.integral_mul_const]
    rw [hval]
    have hpow : (∫ σ in (0 : ℝ)..τ, (-σ) ^ k) = -(-τ) ^ (k + 1) / (k + 1) := by
      have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := τ)
        (fun x : ℝ => x ^ k)
      simp only [neg_zero] at h
      rw [h, integral_pow, zero_pow (Nat.succ_ne_zero k)]
      ring
    have hcint : (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ) ^ k / (k.factorial : ℂ))) =
        - ((-τ : ℂ) ^ (k + 1) / ((k + 1).factorial : ℂ)) := by
      rw [intervalIntegral.integral_div]
      have hcast : (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ)) ^ k) =
          ((∫ σ in (0 : ℝ)..τ, (-σ) ^ k : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        apply intervalIntegral.integral_congr
        intro σ _
        push_cast
        ring
      rw [hcast, hpow, Nat.factorial_succ]
      push_cast
      field_simp
    rw [hcint, neg_smul, neg_neg]

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
