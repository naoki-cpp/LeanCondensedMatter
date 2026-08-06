import LeanCondensedMatter.Analysis.Dyson.Bounds
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson

set_option linter.style.header false

/-!
# Generic specialization and compact bounds for finite Dyson coefficients

This module identifies the transported finite-dimensional Dyson coefficients with the
dimension-independent recursion owned by `Analysis.Dyson`, then supplies the canonical compact
interaction-picture bound needed by the analytic finite-dimensional specialization.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The transported finite-dimensional Dyson coefficient is the generic bounded Dyson coefficient
specialized to the continuous interaction-picture family. -/
theorem continuousDysonCoeff_eq_coeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    continuousDysonCoeff energy V n τ =
      Dyson.coeff (continuousInteractionPicture energy V) n τ := by
  induction n generalizing τ with
  | zero => simp
  | succ n ih =>
      rw [continuousDysonCoeff_succ, Dyson.coeff_succ]
      apply congrArg Neg.neg
      apply intervalIntegral.integral_congr
      intro σ _
      change continuousInteractionPicture energy V σ *
          continuousDysonCoeff energy V n σ =
        continuousInteractionPicture energy V σ *
          Dyson.coeff (continuousInteractionPicture energy V) n σ
      rw [ih]

/-- The norm of the interaction-picture operator is bounded by the product of the three
operator norms in its free-evolution conjugation formula. -/
theorem norm_continuousInteractionPicture_le_conj (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    ‖continuousInteractionPicture energy V τ‖ ≤
      ‖continuousDiagonalEvolution energy τ‖ *
        (‖finiteContinuousOperator V‖ * ‖continuousDiagonalEvolution energy (-τ)‖) := by
  rw [continuousInteractionPicture_eq_conj]
  exact (continuousDiagonalEvolution energy τ).opNorm_comp_le
    ((finiteContinuousOperator V).comp (continuousDiagonalEvolution energy (-τ)))
    |>.trans (mul_le_mul_of_nonneg_left
      ((finiteContinuousOperator V).opNorm_comp_le
        (continuousDiagonalEvolution energy (-τ)))
      (norm_nonneg _))

/-- On a nonempty compact imaginary-time interval, the interaction-picture operator norm has a
uniform nonnegative upper bound. -/
theorem exists_interactionPictureNormBound (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ ∈ Icc (0 : ℝ) β, ‖continuousInteractionPicture energy V τ‖ ≤ M := by
  have hcont : Continuous (fun τ : ℝ => ‖continuousInteractionPicture energy V τ‖) :=
    continuous_norm.comp (continuous_continuousInteractionPicture energy V)
  obtain ⟨τmax, hτmax, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hβ) hcont.continuousOn
  exact ⟨‖continuousInteractionPicture energy V τmax‖, norm_nonneg _,
    fun τ hτ => hmax hτ⟩

/-- A canonical, choice-based uniform interaction-picture norm bound on `[0, β]`.
It is defined as zero when `β < 0`, a case excluded by all bound theorems below. -/
noncomputable def interactionPictureNormBound (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (β : ℝ) : ℝ :=
  if hβ : 0 ≤ β then Classical.choose (exists_interactionPictureNormBound energy V hβ) else 0

/-- The canonical interaction-picture bound is nonnegative on a nonnegative interval. -/
theorem interactionPictureNormBound_nonneg (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ interactionPictureNormBound energy V β := by
  rw [interactionPictureNormBound, dif_pos hβ]
  exact (Classical.choose_spec (exists_interactionPictureNormBound energy V hβ)).1

/-- Uniform interaction-picture norm control on `[0, β]`. -/
theorem norm_continuousInteractionPicture_le (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖continuousInteractionPicture energy V τ‖ ≤ interactionPictureNormBound energy V β := by
  rw [interactionPictureNormBound, dif_pos hβ]
  exact (Classical.choose_spec (exists_interactionPictureNormBound energy V hβ)).2 τ hτ

end
end Common
end SecondQuantization
