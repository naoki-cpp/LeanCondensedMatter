import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionStrongLimit
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Bundled strong-limit Stone evolution

The preceding resolvent construction gives, for every fixed time `t` and vector `x`, the strong
limit of the bounded self-adjoint approximating evolutions.  This file passes linearity and norm
preservation through that limit and bundles the result as a continuous linear operator.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized bounded approximating evolution preserves vector norms. -/
theorem resolventApproximationEvolutionAtScale_apply_norm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) (x : H) :
    ‖resolventApproximationEvolutionAtScale A hA r t x‖ = ‖x‖ := by
  unfold resolventApproximationEvolutionAtScale resolventApproximationEvolution
  apply boundedUnitaryEvolution_apply_norm
  exact boundedSelfAdjointApproximation_isSelfAdjoint A hA _ _

/-- The strong-limit Stone evolution preserves vector norms. -/
theorem resolventEvolutionStrongLimit_apply_norm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    ‖resolventEvolutionStrongLimit A hA t x‖ = ‖x‖ := by
  have hlimit := (tendsto_resolventApproximationEvolutionAtScale_apply A hA t x).norm
  have hconst : Tendsto (fun _ : ℝ => ‖x‖) atTop (𝓝 ‖x‖) := tendsto_const_nhds
  have happ :
      Tendsto (fun r : ℝ => ‖resolventApproximationEvolutionAtScale A hA r t x‖) atTop
        (𝓝 ‖x‖) := by
    simpa only [resolventApproximationEvolutionAtScale_apply_norm] using hconst
  exact tendsto_nhds_unique hlimit happ

/-- The vectorwise Stone limit, bundled as a bounded complex-linear operator.

The approximating evolutions are uniformly bounded in operator norm by one, so Mathlib's general
pointwise-limit construction for bounded families of continuous linear maps applies directly. -/
noncomputable def stoneEvolution
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) : H →L[ℂ] H :=
  ContinuousLinearMap.ofTendstoOfBoundedRange
    (resolventEvolutionStrongLimit A hA t)
    (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t)
    (by
      rw [tendsto_pi_nhds]
      exact fun x => tendsto_resolventApproximationEvolutionAtScale_apply A hA t x)
    (by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨1, ?_⟩
      intro T hT
      obtain ⟨r, rfl⟩ := hT
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      rw [resolventApproximationEvolutionAtScale_apply_norm, one_mul])

@[simp]
theorem stoneEvolution_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    stoneEvolution A hA t x =
      resolventEvolutionStrongLimit A hA t x := by
  rfl

/-- The bundled limiting evolution is an isometry. -/
theorem stoneEvolution_dist_eq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x y : H) :
    dist (stoneEvolution A hA t x)
        (stoneEvolution A hA t y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← (stoneEvolution A hA t).map_sub]
  simpa using resolventEvolutionStrongLimit_apply_norm A hA t (x - y)

end

end LinearPMap
