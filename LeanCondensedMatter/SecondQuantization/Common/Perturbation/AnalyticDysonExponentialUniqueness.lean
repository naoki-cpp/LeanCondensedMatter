import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonExponentialIdentity

set_option linter.style.header false

/-!
# ODE uniqueness for the analytic Dyson evolution

The interaction-picture vector field is extended from `[0, β]` to the whole real line by projecting
time to the compact interval. Its dependence on the operator is globally Lipschitz with the
uniform interaction-picture norm bound.
-/

namespace SecondQuantization
namespace Common

open Set

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The interaction-picture Dyson vector field, with time projected to `[0, β]`. -/
noncomputable def analyticDysonVectorField (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (β : ℝ) (hβ : 0 ≤ β) (lam : ℂ)
    (τ : ℝ) (U : FiniteContinuousOperator Config) : FiniteContinuousOperator Config :=
  -(lam • (continuousInteractionPicture energy V
    (projIcc (0 : ℝ) β hβ τ : ℝ)).comp U)

/-- The projected Dyson vector field is uniformly Lipschitz in the operator variable. -/
theorem lipschitzWith_analyticDysonVectorField (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (β : ℝ) (hβ : 0 ≤ β) (lam : ℂ) (τ : ℝ) :
    LipschitzWith
      (Real.toNNReal (‖lam‖ * interactionPictureNormBound energy V β))
      (analyticDysonVectorField energy V β hβ lam τ) := by
  apply LipschitzWith.of_dist_le'
  intro U W
  let A := continuousInteractionPicture energy V
    (projIcc (0 : ℝ) β hβ τ : ℝ)
  have hcomp : A.comp U - A.comp W = A.comp (U - W) := by
    ext x
    simp
  have hneg :
      -(lam • A.comp U) - -(lam • A.comp W) =
        -(lam • (A.comp U - A.comp W)) := by
    abel_nf
  rw [show analyticDysonVectorField energy V β hβ lam τ U = -(lam • A.comp U) by rfl,
    show analyticDysonVectorField energy V β hβ lam τ W = -(lam • A.comp W) by rfl,
    dist_eq_norm, dist_eq_norm, hneg, norm_neg, ← smul_sub, hcomp, norm_smul]
  calc
    ‖lam‖ * ‖A.comp (U - W)‖ ≤
        ‖lam‖ * (‖A‖ * ‖U - W‖) := by
      gcongr
      exact A.opNorm_comp_le (U - W)
    _ ≤ (‖lam‖ * interactionPictureNormBound energy V β) * ‖U - W‖ := by
      gcongr
      exact norm_continuousInteractionPicture_le energy V hβ
        (projIcc (0 : ℝ) β hβ τ).property

/-- On `[0, β]`, the projected vector field is the original interaction-picture field. -/
theorem analyticDysonVectorField_of_mem (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (β : ℝ) (hβ : 0 ≤ β) (lam : ℂ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) β) (U : FiniteContinuousOperator Config) :
    analyticDysonVectorField energy V β hβ lam τ U =
      -(lam • (continuousInteractionPicture energy V τ).comp U) := by
  rw [analyticDysonVectorField, projIcc_of_mem hβ hτ]

/-- The analytic Dyson sum solves the projected vector field on `[0, β)`. -/
theorem hasDerivWithinAt_analyticDysonEvolution_vectorField
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Ico (0 : ℝ) β) (lam : ℂ) :
    HasDerivWithinAt (fun σ : ℝ => analyticDysonEvolution energy V σ lam)
      (analyticDysonVectorField energy V β hβ lam τ
        (analyticDysonEvolution energy V τ lam)) (Ici τ) τ := by
  rw [analyticDysonVectorField_of_mem energy V β hβ lam
    (Ico_subset_Icc_self hτ)]
  exact hasDerivWithinAt_analyticDysonEvolution_interactionPicture
    energy V hβ hτ lam

/-- The ordered exponential candidate solves the projected vector field on `[0, β)`. -/
theorem hasDerivWithinAt_analyticDysonExponentialCandidate_vectorField
    (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Ico (0 : ℝ) β) (lam : ℂ) :
    HasDerivWithinAt
      (fun σ : ℝ => analyticDysonExponentialCandidate energy V σ lam)
      (analyticDysonVectorField energy V β hβ lam τ
        (analyticDysonExponentialCandidate energy V τ lam)) (Ici τ) τ := by
  rw [analyticDysonVectorField_of_mem energy V β hβ lam
    (Ico_subset_Icc_self hτ)]
  change HasDerivWithinAt
    (fun σ : ℝ => analyticDysonExponentialCandidate energy V σ lam)
    (-(lam • (continuousInteractionPicture energy V τ *
      analyticDysonExponentialCandidate energy V τ lam))) (Ici τ) τ
  exact (hasDerivAt_analyticDysonExponentialCandidate_interactionPicture
    energy V τ lam).hasDerivWithinAt

/-- On every compact nonnegative time interval, the analytic Dyson sum equals the exact ordered
operator-exponential candidate. -/
theorem analyticDysonEvolution_eq_exponentialCandidate (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    analyticDysonEvolution energy V τ lam =
      analyticDysonExponentialCandidate energy V τ lam := by
  let K : ℝ≥0 :=
    Real.toNNReal (‖lam‖ * interactionPictureNormBound energy V β)
  let v : ℝ → FiniteContinuousOperator Config → FiniteContinuousOperator Config :=
    analyticDysonVectorField energy V β hβ lam
  have hv : ∀ t, LipschitzWith K (v t) := by
    intro t
    exact lipschitzWith_analyticDysonVectorField energy V β hβ lam t
  have hf : ContinuousOn
      (fun t : ℝ => analyticDysonEvolution energy V t lam) (Icc (0 : ℝ) β) :=
    continuousOn_analyticDysonEvolution energy V hβ lam
  have hf' : ∀ t ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt (fun s : ℝ => analyticDysonEvolution energy V s lam)
        (v t (analyticDysonEvolution energy V t lam)) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_analyticDysonEvolution_vectorField
      energy V hβ ht lam
  have hg : ContinuousOn
      (fun t : ℝ => analyticDysonExponentialCandidate energy V t lam)
      (Icc (0 : ℝ) β) :=
    (continuous_analyticDysonExponentialCandidate energy V lam).continuousOn
  have hg' : ∀ t ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt
        (fun s : ℝ => analyticDysonExponentialCandidate energy V s lam)
        (v t (analyticDysonExponentialCandidate energy V t lam)) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_analyticDysonExponentialCandidate_vectorField
      energy V hβ ht lam
  have heq : EqOn
      (fun t : ℝ => analyticDysonEvolution energy V t lam)
      (fun t : ℝ => analyticDysonExponentialCandidate energy V t lam)
      (Icc (0 : ℝ) β) :=
    ODE_solution_unique hv hf hf' hg hg' (by simp)
  exact heq hτ

end
end Common
end SecondQuantization
