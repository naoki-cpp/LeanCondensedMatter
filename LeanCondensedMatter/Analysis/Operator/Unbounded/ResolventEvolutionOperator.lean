import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionStrongLimit
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
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

/-- Additivity passes from the bounded approximants to their vectorwise strong limit. -/
theorem resolventEvolutionStrongLimit_add
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x y : H) :
    resolventEvolutionStrongLimit A hA t (x + y) =
      resolventEvolutionStrongLimit A hA t x + resolventEvolutionStrongLimit A hA t y := by
  have hxy := tendsto_resolventApproximationEvolutionAtScale_apply A hA t (x + y)
  have hsum :=
    (tendsto_resolventApproximationEvolutionAtScale_apply A hA t x).add
      (tendsto_resolventApproximationEvolutionAtScale_apply A hA t y)
  exact tendsto_nhds_unique hxy <|
    hsum.congr' (Eventually.of_forall fun r =>
      ((resolventApproximationEvolutionAtScale A hA r t).map_add x y).symm)

/-- Complex scalar multiplication passes from the bounded approximants to their strong limit. -/
theorem resolventEvolutionStrongLimit_smul
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (c : ℂ) (x : H) :
    resolventEvolutionStrongLimit A hA t (c • x) =
      c • resolventEvolutionStrongLimit A hA t x := by
  have hcx := tendsto_resolventApproximationEvolutionAtScale_apply A hA t (c • x)
  have hc : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hsmul := hc.smul
    (tendsto_resolventApproximationEvolutionAtScale_apply A hA t x)
  exact tendsto_nhds_unique hcx <|
    hsmul.congr' (Eventually.of_forall fun r =>
      ((resolventApproximationEvolutionAtScale A hA r t).map_smul c x).symm)

/-- The vectorwise strong limit is a complex linear map. -/
noncomputable def resolventEvolutionStrongLimitLinearMap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) : H →ₗ[ℂ] H where
  toFun := resolventEvolutionStrongLimit A hA t
  map_add' := resolventEvolutionStrongLimit_add A hA t
  map_smul' := resolventEvolutionStrongLimit_smul A hA t

@[simp]
theorem resolventEvolutionStrongLimitLinearMap_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    resolventEvolutionStrongLimitLinearMap A hA t x =
      resolventEvolutionStrongLimit A hA t x := by
  rfl

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

/-- The vectorwise Stone limit, bundled as a bounded complex-linear operator. -/
noncomputable def resolventEvolutionStrongLimitOperator
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) : H →L[ℂ] H :=
  (resolventEvolutionStrongLimitLinearMap A hA t).mkContinuous 1 (by
    intro x
    simp [resolventEvolutionStrongLimit_apply_norm])

@[simp]
theorem resolventEvolutionStrongLimitOperator_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    resolventEvolutionStrongLimitOperator A hA t x =
      resolventEvolutionStrongLimit A hA t x := by
  rfl

/-- The bundled limiting evolution is an isometry. -/
theorem resolventEvolutionStrongLimitOperator_dist_eq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x y : H) :
    dist (resolventEvolutionStrongLimitOperator A hA t x)
        (resolventEvolutionStrongLimitOperator A hA t y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← (resolventEvolutionStrongLimitOperator A hA t).map_sub]
  simpa using resolventEvolutionStrongLimit_apply_norm A hA t (x - y)

end

end LinearPMap
