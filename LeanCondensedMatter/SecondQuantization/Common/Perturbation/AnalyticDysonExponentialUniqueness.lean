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

end
end Common
end SecondQuantization
