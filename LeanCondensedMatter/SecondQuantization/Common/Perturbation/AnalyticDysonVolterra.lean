import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDyson
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option linter.style.header false

/-!
# Volterra equation for the analytic Dyson evolution

The factorial majorant controls the interaction-picture integrand uniformly on compact imaginary-
time intervals. Mathlib's dominated-convergence theorem therefore exchanges the operator-valued
Dyson series with the Bochner interval integral.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The `n`th term in the Volterra integrand, including the external coupling `λ`. -/
noncomputable def analyticDysonIntegrand (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (lam : ℂ) (n : ℕ) (σ : ℝ) : FiniteContinuousOperator Config :=
  lam • (continuousInteractionPicture energy V σ).comp
    (analyticDysonTerm energy V σ lam n)

/-- A constant-in-time summable majorant for the Volterra integrand on `[0, β]`. -/
noncomputable def analyticDysonIntegrandMajorant (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (β : ℝ) (lam : ℂ) (n : ℕ) : ℝ :=
  (‖lam‖ * interactionPictureNormBound energy V β) *
    dysonMajorant
      (‖lam‖ * interactionPictureNormBound energy V β) β n

/-- Every weighted Dyson coefficient is continuous in imaginary time. -/
theorem continuous_analyticDysonTerm (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (lam : ℂ) (n : ℕ) :
    Continuous (fun τ => analyticDysonTerm energy V τ lam n) := by
  exact continuous_const.smul (continuous_continuousDysonCoeff energy V n)

/-- Every term of the Volterra integrand is continuous. -/
theorem continuous_analyticDysonIntegrand (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (lam : ℂ) (n : ℕ) :
    Continuous (analyticDysonIntegrand energy V lam n) := by
  simpa only [analyticDysonIntegrand] using
    continuous_const.smul
      ((continuous_continuousInteractionPicture energy V).clm_comp
        (continuous_analyticDysonTerm energy V lam n))

/-- Left composition by the interaction-picture operator and scalar multiplication by `λ`
carry the Dyson `HasSum` to the pointwise Volterra integrand. -/
theorem hasSum_analyticDysonIntegrand (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β σ : ℝ}
    (hβ : 0 ≤ β) (hσ : σ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (fun n => analyticDysonIntegrand energy V lam n σ)
      (lam • (continuousInteractionPicture energy V σ).comp
        (analyticDysonEvolution energy V σ lam)) := by
  have hcomp :=
    (ContinuousLinearMap.compL ℂ
      (FiniteAnalyticFock Config) (FiniteAnalyticFock Config) (FiniteAnalyticFock Config)
      (continuousInteractionPicture energy V σ)).hasSum
      (hasSum_analyticDysonEvolution energy V hβ hσ lam)
  simpa only [analyticDysonIntegrand, ContinuousLinearMap.compL_apply] using
    hcomp.const_smul lam

/-- The Volterra-integrand majorant is summable. -/
theorem summable_analyticDysonIntegrandMajorant (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (β : ℝ) (lam : ℂ) :
    Summable (analyticDysonIntegrandMajorant energy V β lam) := by
  exact (summable_dysonMajorant
    (‖lam‖ * interactionPictureNormBound energy V β) β).mul_left
      (‖lam‖ * interactionPictureNormBound energy V β)

/-- Uniform pointwise norm control of every Volterra-integrand term on `[0, β]`. -/
theorem norm_analyticDysonIntegrand_le (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β σ : ℝ}
    (hβ : 0 ≤ β) (hσ : σ ∈ Icc (0 : ℝ) β) (lam : ℂ) (n : ℕ) :
    ‖analyticDysonIntegrand energy V lam n σ‖ ≤
      analyticDysonIntegrandMajorant energy V β lam n := by
  have hM : 0 ≤ interactionPictureNormBound energy V β :=
    interactionPictureNormBound_nonneg energy V hβ
  have hweighted : 0 ≤ ‖lam‖ * interactionPictureNormBound energy V β :=
    mul_nonneg (norm_nonneg lam) hM
  have hterm : ‖analyticDysonTerm energy V σ lam n‖ ≤
      dysonMajorant
        (‖lam‖ * interactionPictureNormBound energy V β) β n :=
    (norm_analyticDysonTerm_le energy V hβ hσ lam n).trans
      (dysonMajorant_mono_tau hweighted hσ.1 hσ.2 n)
  calc
    ‖analyticDysonIntegrand energy V lam n σ‖ =
        ‖lam‖ * ‖(continuousInteractionPicture energy V σ).comp
          (analyticDysonTerm energy V σ lam n)‖ := by
      rw [analyticDysonIntegrand, norm_smul]
    _ ≤ ‖lam‖ *
        (‖continuousInteractionPicture energy V σ‖ *
          ‖analyticDysonTerm energy V σ lam n‖) :=
      mul_le_mul_of_nonneg_left
        ((continuousInteractionPicture energy V σ).opNorm_comp_le
          (analyticDysonTerm energy V σ lam n))
        (norm_nonneg lam)
    _ ≤ ‖lam‖ *
        (interactionPictureNormBound energy V β *
          dysonMajorant
            (‖lam‖ * interactionPictureNormBound energy V β) β n) := by
      gcongr
      exact norm_continuousInteractionPicture_le energy V hβ hσ
    _ = analyticDysonIntegrandMajorant energy V β lam n := by
      rw [analyticDysonIntegrandMajorant]
      ring

/-- The Volterra integrand series may be exchanged with the Bochner interval integral. -/
theorem hasSum_intervalIntegral_analyticDysonIntegrand (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum
      (fun n => ∫ σ in (0 : ℝ)..τ, analyticDysonIntegrand energy V lam n σ)
      (∫ σ in (0 : ℝ)..τ,
        lam • (continuousInteractionPicture energy V σ).comp
          (analyticDysonEvolution energy V σ lam)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => analyticDysonIntegrandMajorant energy V β lam n)
  · intro n
    exact (continuous_analyticDysonIntegrand energy V lam n).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun σ hσ => by
      have hσ' : σ ∈ Icc (0 : ℝ) τ := by
        simpa [uIcc_of_le hτ.1] using (uIoc_subset_uIcc hσ)
      exact norm_analyticDysonIntegrand_le energy V hβ
        ⟨hσ'.1, hσ'.2.trans hτ.2⟩ lam n
  · exact Filter.Eventually.of_forall fun _ _ =>
      summable_analyticDysonIntegrandMajorant energy V β lam
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun σ hσ => by
      have hσ' : σ ∈ Icc (0 : ℝ) τ := by
        simpa [uIcc_of_le hτ.1] using (uIoc_subset_uIcc hσ)
      exact hasSum_analyticDysonIntegrand energy V hβ
        ⟨hσ'.1, hσ'.2.trans hτ.2⟩ lam

/-- Integrating the `n`th Volterra term gives the negative `(n+1)`st Dyson term. -/
theorem intervalIntegral_analyticDysonIntegrand (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (lam : ℂ) (n : ℕ) :
    (∫ σ in (0 : ℝ)..τ, analyticDysonIntegrand energy V lam n σ) =
      - analyticDysonTerm energy V τ lam (n + 1) := by
  rw [analyticDysonTerm, continuousDysonCoeff_succ, smul_neg, neg_neg]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro σ _
  ext x
  simp [analyticDysonIntegrand, analyticDysonTerm, pow_succ', smul_smul]

/-- The positive-order Dyson tail sums to the negative Volterra integral. -/
theorem hasSum_analyticDysonTail (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (fun n => analyticDysonTerm energy V τ lam (n + 1))
      (- ∫ σ in (0 : ℝ)..τ,
        lam • (continuousInteractionPicture energy V σ).comp
          (analyticDysonEvolution energy V σ lam)) := by
  have hneg := hasSum_intervalIntegral_analyticDysonIntegrand energy V hβ hτ lam
  have hfun :
      (fun n => ∫ σ in (0 : ℝ)..τ, analyticDysonIntegrand energy V lam n σ) =
        fun n => - analyticDysonTerm energy V τ lam (n + 1) := by
    funext n
    exact intervalIntegral_analyticDysonIntegrand energy V τ lam n
  rw [hfun] at hneg
  simpa only [neg_neg] using hneg.neg

/-- The analytic Dyson evolution solves the interaction-picture Volterra equation. -/
theorem analyticDysonEvolution_eq_one_sub_integral (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    analyticDysonEvolution energy V τ lam =
      1 - lam • ∫ σ in (0 : ℝ)..τ,
        (continuousInteractionPicture energy V σ).comp
          (analyticDysonEvolution energy V σ lam) := by
  have hfull := hasSum_analyticDysonEvolution energy V hβ hτ lam
  have hdecomp : HasSum (analyticDysonTerm energy V τ lam)
      (analyticDysonTerm energy V τ lam 0 +
        (- ∫ σ in (0 : ℝ)..τ,
          lam • (continuousInteractionPicture energy V σ).comp
            (analyticDysonEvolution energy V σ lam))) :=
    (hasSum_analyticDysonTail energy V hβ hτ lam).zero_add
  have heq := hfull.unique hdecomp
  simpa [analyticDysonTerm, sub_eq_add_neg, intervalIntegral.integral_smul] using heq

end
end Common
end SecondQuantization
