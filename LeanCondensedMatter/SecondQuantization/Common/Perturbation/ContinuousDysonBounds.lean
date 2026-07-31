import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

set_option linter.style.header false

/-!
# Norm bounds for continuous finite-dimensional Dyson coefficients

This module proves the factorial majorant required for convergence of the finite-mode Dyson
series. The interaction-picture norm bound is obtained from the extreme-value theorem on the
compact interval `[0, β]`; no coordinate-dependent matrix norm is introduced.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-! ## Interaction-picture norm bounds -/

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

/-! ## Factorial majorants -/

/-- The scalar exponential-series majorant `(M τ)ⁿ / n!`. -/
noncomputable def dysonMajorant (M τ : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ)⁻¹ * (M * τ) ^ n

@[simp]
theorem dysonMajorant_zero (M τ : ℝ) : dysonMajorant M τ 0 = 1 := by
  simp [dysonMajorant]

/-- The Dyson majorant is nonnegative for nonnegative `M` and `τ`. -/
theorem dysonMajorant_nonneg {M τ : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ) (n : ℕ) :
    0 ≤ dysonMajorant M τ n := by
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (pow_nonneg (mul_nonneg hM hτ) n)

/-- Integrating one more interaction-picture factor advances the factorial majorant by one order. -/
theorem integral_mul_dysonMajorant (M τ : ℝ) (n : ℕ) :
    ∫ σ in (0 : ℝ)..τ, M * dysonMajorant M σ n = dysonMajorant M τ (n + 1) := by
  have hfun : (fun σ : ℝ => M * dysonMajorant M σ n) =
      fun σ : ℝ => ((n.factorial : ℝ)⁻¹ * M ^ (n + 1)) * σ ^ n := by
    funext σ
    simp only [dysonMajorant, mul_pow]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, dysonMajorant,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
  field_simp [Nat.factorial_ne_zero]

/-- The scalar factorial majorant is summable for every real `M` and `τ`. -/
theorem summable_dysonMajorant (M τ : ℝ) : Summable (dysonMajorant M τ) := by
  simpa [dysonMajorant, div_eq_mul_inv, mul_comm] using
    Real.summable_pow_div_factorial (M * τ)

/-- A uniform interaction-picture bound `M` implies the standard factorial Dyson coefficient
bound on `[0, β]`. -/
theorem norm_continuousDysonCoeff_le_of_bound (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β M : ℝ}
    (hM : 0 ≤ M)
    (hVI : ∀ σ ∈ Icc (0 : ℝ) β, ‖continuousInteractionPicture energy V σ‖ ≤ M)
    (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖continuousDysonCoeff energy V n τ‖ ≤ dysonMajorant M τ n := by
  induction n generalizing τ with
  | zero =>
      rw [continuousDysonCoeff_zero, dysonMajorant_zero]
      change ‖ContinuousLinearMap.id ℂ (FiniteAnalyticFock Config)‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [continuousDysonCoeff_succ, norm_neg]
      calc
        ‖∫ σ in (0 : ℝ)..τ,
            (continuousInteractionPicture energy V σ).comp
              (continuousDysonCoeff energy V n σ)‖ ≤
            ∫ σ in (0 : ℝ)..τ, M * dysonMajorant M σ n := by
          apply intervalIntegral.norm_integral_le_of_norm_le hτ.1
          · refine Filter.Eventually.of_forall fun σ hσ => ?_
            have hσβ : σ ∈ Icc (0 : ℝ) β := ⟨hσ.1.le, hσ.2.trans hτ.2⟩
            calc
              ‖(continuousInteractionPicture energy V σ).comp
                  (continuousDysonCoeff energy V n σ)‖ ≤
                  ‖continuousInteractionPicture energy V σ‖ *
                    ‖continuousDysonCoeff energy V n σ‖ :=
                (continuousInteractionPicture energy V σ).opNorm_comp_le
                  (continuousDysonCoeff energy V n σ)
              _ ≤ M * dysonMajorant M σ n :=
                mul_le_mul (hVI σ hσβ) (ih hσβ) (norm_nonneg _) hM
          · have hcont : Continuous (fun σ : ℝ => M * dysonMajorant M σ n) := by
              unfold dysonMajorant
              fun_prop
            exact hcont.intervalIntegrable 0 τ
        _ = dysonMajorant M τ (n + 1) := integral_mul_dysonMajorant M τ n

/-- The canonical compact-interval bound gives the factorial estimate for every continuous Dyson
coefficient. -/
theorem norm_continuousDysonCoeff_le (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (n : ℕ) (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖continuousDysonCoeff energy V n τ‖ ≤
      dysonMajorant (interactionPictureNormBound energy V β) τ n :=
  norm_continuousDysonCoeff_le_of_bound energy V
    (interactionPictureNormBound_nonneg energy V hβ)
    (fun _ hσ => norm_continuousInteractionPicture_le energy V hβ hσ) n hτ

/-- The norms of the perturbatively weighted Dyson coefficients are summable on every compact
imaginary-time interval. This is the reusable Weierstrass majorant for the analytic Dyson series. -/
theorem summable_norm_pow_smul_continuousDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    Summable (fun n : ℕ => ‖lam ^ n • continuousDysonCoeff energy V n τ‖) := by
  have hmaj : Summable
      (dysonMajorant (‖lam‖ * interactionPictureNormBound energy V β) τ) :=
    summable_dysonMajorant _ _
  refine hmaj.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  calc
    ‖lam ^ n • continuousDysonCoeff energy V n τ‖ =
        ‖lam‖ ^ n * ‖continuousDysonCoeff energy V n τ‖ := by
      rw [norm_smul, norm_pow]
    _ ≤ ‖lam‖ ^ n *
        dysonMajorant (interactionPictureNormBound energy V β) τ n :=
      mul_le_mul_of_nonneg_left (norm_continuousDysonCoeff_le energy V hβ n hτ)
        (pow_nonneg (norm_nonneg lam) n)
    _ = dysonMajorant (‖lam‖ * interactionPictureNormBound energy V β) τ n := by
      simp only [dysonMajorant]
      ring_nf

end
end Common
end SecondQuantization
