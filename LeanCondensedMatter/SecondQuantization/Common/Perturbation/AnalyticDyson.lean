import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDysonBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

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

/-- The weighted `n`th coefficient is controlled by the exponential majorant inherited from
`ContinuousDysonBounds`. -/
theorem norm_analyticDysonTerm_le (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Set.Icc (0 : ℝ) β) (lam : ℂ) (n : ℕ) :
    ‖analyticDysonTerm energy V τ lam n‖ ≤
      dysonMajorant
        (‖lam‖ * interactionPictureNormBound energy V β) τ n := by
  calc
    ‖analyticDysonTerm energy V τ lam n‖ =
        ‖lam‖ ^ n * ‖continuousDysonCoeff energy V n τ‖ := by
      rw [analyticDysonTerm, norm_smul, norm_pow]
    _ ≤ ‖lam‖ ^ n *
        dysonMajorant (interactionPictureNormBound energy V β) τ n :=
      mul_le_mul_of_nonneg_left
        (norm_continuousDysonCoeff_le energy V hβ n hτ)
        (pow_nonneg (norm_nonneg lam) n)
    _ = dysonMajorant
        (‖lam‖ * interactionPictureNormBound energy V β) τ n := by
      simp only [dysonMajorant]
      ring_nf

/-- The factorial majorant is monotone in nonnegative imaginary time. -/
theorem dysonMajorant_mono_tau {M τ β : ℝ} (hM : 0 ≤ M)
    (hτ : 0 ≤ τ) (hτβ : τ ≤ β) (n : ℕ) :
    dysonMajorant M τ n ≤ dysonMajorant M β n := by
  unfold dysonMajorant
  gcongr

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

/-- The analytic Dyson series converges uniformly in operator norm on every compact interval
`[0, β]`. -/
theorem hasSumUniformlyOn_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    HasSumUniformlyOn
      (fun n τ => analyticDysonTerm energy V τ lam n)
      (fun τ => analyticDysonEvolution energy V τ lam)
      (Set.Icc (0 : ℝ) β) := by
  have hM : 0 ≤ ‖lam‖ * interactionPictureNormBound energy V β :=
    mul_nonneg (norm_nonneg lam)
      (interactionPictureNormBound_nonneg energy V hβ)
  simpa only [analyticDysonEvolution] using
    (HasSumUniformlyOn.of_norm_le_summable
      (f := fun n τ => analyticDysonTerm energy V τ lam n)
      (u := dysonMajorant
        (‖lam‖ * interactionPictureNormBound energy V β) β)
      (summable_dysonMajorant _ _)
      (fun n τ hτ =>
        (norm_analyticDysonTerm_le energy V hβ hτ lam n).trans
          (dysonMajorant_mono_tau hM hτ.1 hτ.2 n)))

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
