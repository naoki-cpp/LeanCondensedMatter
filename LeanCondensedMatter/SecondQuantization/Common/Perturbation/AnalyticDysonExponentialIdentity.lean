import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Identification of the analytic Dyson evolution with operator exponentials

The Dyson sum and the ordered operator-exponential candidate are identified as the unique solutions
of the same interaction-picture initial-value problem on each compact nonnegative time interval.
-/

namespace SecondQuantization
namespace Common

open Set Filter
open scoped Topology

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The analytic Dyson evolution is continuous on every compact nonnegative time interval. -/
theorem continuousOn_analyticDysonEvolution (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    ContinuousOn (fun τ => analyticDysonEvolution energy V τ lam) (Icc (0 : ℝ) β) := by
  apply (hasSumUniformlyOn_analyticDysonEvolution energy V hβ lam).tendstoUniformlyOn.continuousOn
  exact (Filter.Eventually.of_forall fun s =>
    (continuous_finsetSum s fun n _ =>
      continuous_analyticDysonTerm energy V lam n).continuousOn).frequently

/-- The exact operator-exponential candidate is continuous in imaginary time. -/
theorem continuous_analyticDysonExponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    Continuous (fun τ : ℝ => analyticDysonExponentialCandidate energy V τ lam) :=
  continuous_iff_continuousAt.2 fun τ =>
    (hasDerivAt_analyticDysonExponentialCandidate_interactionPicture energy V τ lam).continuousAt

/-- The interaction-picture product with the analytic Dyson evolution is continuous on every
compact nonnegative time interval. -/
theorem continuousOn_interactionPicture_mul_analyticDysonEvolution
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β : ℝ}
    (hβ : 0 ≤ β) (lam : ℂ) :
    ContinuousOn (fun τ => continuousInteractionPicture energy V τ *
      analyticDysonEvolution energy V τ lam) (Icc (0 : ℝ) β) := by
  change ContinuousOn (fun τ =>
    (continuousInteractionPicture energy V τ).comp
      (analyticDysonEvolution energy V τ lam)) (Icc (0 : ℝ) β)
  exact (continuous_continuousInteractionPicture energy V).continuousOn.clm_comp
    (continuousOn_analyticDysonEvolution energy V hβ lam)

/-- On the half-open interval `[0, β)`, the analytic Dyson evolution solves the
interaction-picture differential equation as a right derivative. -/
theorem hasDerivWithinAt_analyticDysonEvolution_interactionPicture
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Ico (0 : ℝ) β) (lam : ℂ) :
    HasDerivWithinAt (fun σ : ℝ => analyticDysonEvolution energy V σ lam)
      (-(lam • (continuousInteractionPicture energy V τ *
        analyticDysonEvolution energy V τ lam))) (Ici τ) τ := by
  let g : ℝ → FiniteContinuousOperator Config := fun σ =>
    (continuousInteractionPicture energy V σ).comp
      (analyticDysonEvolution energy V σ lam)
  have hg : ContinuousOn g (Icc (0 : ℝ) β) := by
    simpa only [g] using
      continuousOn_interactionPicture_mul_analyticDysonEvolution energy V hβ lam
  let p : ℝ → ℝ := fun x => (projIcc (0 : ℝ) β hβ x : ℝ)
  let gExt : ℝ → FiniteContinuousOperator Config := fun x => g (p x)
  have hp : Continuous p := by
    exact continuous_subtype_val.comp (LipschitzWith.projIcc hβ).continuous
  have hpmap : MapsTo p univ (Icc (0 : ℝ) β) := by
    intro x _
    exact (projIcc (0 : ℝ) β hβ x).property
  have hgExt : Continuous gExt := by
    apply continuousOn_univ.mp
    exact hg.comp hp.continuousOn hpmap
  have hgExt_eq : EqOn gExt g (Icc (0 : ℝ) β) := by
    intro x hx
    change g (p x) = g x
    rw [show p x = x by
      change ((projIcc (0 : ℝ) β hβ x : Icc (0 : ℝ) β) : ℝ) = x
      rw [projIcc_of_mem hβ hx]]
  have hτIcc : τ ∈ Icc (0 : ℝ) β := ⟨hτ.1, hτ.2.le⟩
  have hFTC0 := (hgExt.integral_hasDerivAt (0 : ℝ) τ).hasDerivWithinAt
  have hFTC : HasDerivWithinAt (fun u => ∫ σ in (0 : ℝ)..u, gExt σ)
      (g τ) (Ici τ) τ :=
    hFTC0.congr_deriv (hgExt_eq hτIcc)
  let rhs : ℝ → FiniteContinuousOperator Config :=
    (fun _ => (1 : FiniteContinuousOperator Config)) -
      lam • (fun u => ∫ σ in (0 : ℝ)..u, gExt σ)
  have hrhs0 :=
    (hasDerivAt_const (x := τ) (c := (1 : FiniteContinuousOperator Config))).hasDerivWithinAt.sub
      (hFTC.const_smul lam)
  change HasDerivWithinAt rhs (0 - lam • g τ) (Ici τ) τ at hrhs0
  have hrhs : HasDerivWithinAt rhs (-(lam • g τ)) (Ici τ) τ :=
    hrhs0.congr_deriv (by simp)
  have hIcc_mem : Icc (0 : ℝ) β ∈ 𝓝[Ici τ] τ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio β, Iio_mem_nhds hτ.2, ?_⟩
    rintro x ⟨hxβ, hτx⟩
    exact ⟨hτ.1.trans hτx, le_of_lt hxβ⟩
  have heq :
      (fun u : ℝ => analyticDysonEvolution energy V u lam) =ᶠ[𝓝[Ici τ] τ] rhs := by
    filter_upwards [hIcc_mem] with u hu
    have huIcc : uIcc (0 : ℝ) u ⊆ Icc (0 : ℝ) β := by
      rw [uIcc_of_le hu.1]
      exact Icc_subset_Icc_right hu.2
    have hintEq :
        (∫ σ in (0 : ℝ)..u, gExt σ) = ∫ σ in (0 : ℝ)..u, g σ := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      exact hgExt_eq (huIcc hσ)
    rw [show rhs u = (1 : FiniteContinuousOperator Config) -
        lam • ∫ σ in (0 : ℝ)..u, gExt σ by rfl, hintEq]
    simpa only [g] using
      analyticDysonEvolution_eq_one_sub_integral energy V hβ hu lam
  have hpoint : analyticDysonEvolution energy V τ lam = rhs τ := by
    have hτuIcc : uIcc (0 : ℝ) τ ⊆ Icc (0 : ℝ) β := by
      rw [uIcc_of_le hτ.1]
      exact Icc_subset_Icc_right hτ.2.le
    have hintEq :
        (∫ σ in (0 : ℝ)..τ, gExt σ) = ∫ σ in (0 : ℝ)..τ, g σ := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      exact hgExt_eq (hτuIcc hσ)
    rw [show rhs τ = (1 : FiniteContinuousOperator Config) -
        lam • ∫ σ in (0 : ℝ)..τ, gExt σ by rfl, hintEq]
    simpa only [g] using
      analyticDysonEvolution_eq_one_sub_integral energy V hβ hτIcc lam
  have hout := hrhs.congr_of_eventuallyEq heq hpoint
  simpa only [g] using hout

end
end Common
end SecondQuantization
