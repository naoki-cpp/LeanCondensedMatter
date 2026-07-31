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

open Set

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
    continuousInteractionPicture energy V σ * analyticDysonEvolution energy V σ lam
  have hg : ContinuousOn g (Icc (0 : ℝ) β) := by
    simpa only [g] using
      continuousOn_interactionPicture_mul_analyticDysonEvolution energy V hβ lam
  have hτIcc : τ ∈ Icc (0 : ℝ) β := ⟨hτ.1, hτ.2.le⟩
  have hgτ : ContinuousWithinAt g (Icc (0 : ℝ) β) τ := hg τ hτIcc
  have hIcc_mem_right : Icc (0 : ℝ) β ∈ 𝓝[Ioi τ] τ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio β, Iio_mem_nhds hτ.2, ?_⟩
    rintro x ⟨hxβ, hτx⟩
    exact ⟨hτ.1.trans (le_of_lt hτx), le_of_lt hxβ⟩
  have hfilter : 𝓝[Ioi τ] τ ≤ 𝓝[Icc (0 : ℝ) β] τ := by
    rw [nhdsWithin, nhdsWithin]
    exact le_inf inf_le_left (le_principal_iff.mpr hIcc_mem_right)
  have hright : ContinuousWithinAt g (Ioi τ) τ := hgτ.mono_left hfilter
  have huIcc : uIcc (0 : ℝ) τ ⊆ Icc (0 : ℝ) β := by
    rw [uIcc_of_le hτ.1]
    exact Icc_subset_Icc_right hτ.2.le
  have hint : IntervalIntegrable g MeasureTheory.volume 0 τ :=
    (hg.mono huIcc).intervalIntegrable
  have hFTC : HasDerivWithinAt (fun u => ∫ σ in (0 : ℝ)..u, g σ) (g τ) (Ici τ) τ :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      hright.stronglyMeasurableAtFilter hright
  have hrhs : HasDerivWithinAt
      (fun u : ℝ => (1 : FiniteContinuousOperator Config) -
        lam • ∫ σ in (0 : ℝ)..u, g σ)
      (-(lam • g τ)) (Ici τ) τ := by
    simpa using
      (hasDerivAt_const (x := τ) (c := (1 : FiniteContinuousOperator Config))).hasDerivWithinAt.sub
        (hFTC.const_smul lam)
  have hIcc_mem : Icc (0 : ℝ) β ∈ 𝓝[Ici τ] τ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio β, Iio_mem_nhds hτ.2, ?_⟩
    rintro x ⟨hxβ, hτx⟩
    exact ⟨hτ.1.trans hτx, le_of_lt hxβ⟩
  have heq :
      (fun u : ℝ => analyticDysonEvolution energy V u lam) =ᶠ[𝓝[Ici τ] τ]
        (fun u : ℝ => (1 : FiniteContinuousOperator Config) -
          lam • ∫ σ in (0 : ℝ)..u, g σ) := by
    filter_upwards [hIcc_mem] with u hu
    simpa only [g] using
      analyticDysonEvolution_eq_one_sub_integral energy V hβ hu lam
  exact hrhs.congr_of_eventuallyEq heq (by
    simpa only [g] using
      analyticDysonEvolution_eq_one_sub_integral energy V hβ hτIcc lam)

end
end Common
end SecondQuantization
