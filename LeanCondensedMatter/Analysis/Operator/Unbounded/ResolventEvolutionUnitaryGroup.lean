import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Unitary-group laws for the strong Stone limit

The bounded resolvent approximations form unitary one-parameter groups and converge strongly at
fixed time.  Uniform isometry control allows composition to pass through this strong limit.  The
resulting bundled limiting operators therefore satisfy the additive group law.  Their already-proved
norm preservation gives inner-product preservation; together with the negative-time inverse this
identifies the Hilbert-space adjoint with negative-time evolution and hence proves unitarity.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized bounded approximants retain the zero-time identity. -/
@[simp]
theorem resolventApproximationEvolutionAtScale_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) :
    resolventApproximationEvolutionAtScale A hA r 0 = 1 := by
  unfold resolventApproximationEvolutionAtScale
  exact resolventApproximationEvolution_zero A hA _ _

/-- The totalized bounded approximants retain the additive one-parameter group law. -/
theorem resolventApproximationEvolutionAtScale_add
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t s : ℝ) :
    resolventApproximationEvolutionAtScale A hA r (t + s) =
      resolventApproximationEvolutionAtScale A hA r t *
        resolventApproximationEvolutionAtScale A hA r s := by
  unfold resolventApproximationEvolutionAtScale
  exact resolventApproximationEvolution_add A hA _ _ t s

/-- The totalized bounded approximants preserve distances. -/
theorem resolventApproximationEvolutionAtScale_dist_eq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) (x y : H) :
    dist (resolventApproximationEvolutionAtScale A hA r t x)
        (resolventApproximationEvolutionAtScale A hA r t y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm,
    ← (resolventApproximationEvolutionAtScale A hA r t).map_sub]
  exact resolventApproximationEvolutionAtScale_apply_norm A hA r t (x - y)

/-- The strong-limit evolution is the identity at time zero, pointwise. -/
theorem resolventEvolutionStrongLimit_zero_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    resolventEvolutionStrongLimit A hA 0 x = x := by
  have hlimit := tendsto_resolventApproximationEvolutionAtScale_apply A hA 0 x
  exact tendsto_nhds_unique hlimit <|
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atTop (𝓝 x)).congr'
      (Eventually.of_forall fun r => by
        rw [resolventApproximationEvolutionAtScale_zero]
        rfl)

/-- The bundled strong-limit evolution is the identity at time zero. -/
@[simp]
theorem resolventEvolutionStrongLimitOperator_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    resolventEvolutionStrongLimitOperator A hA 0 = 1 := by
  ext x
  simpa using resolventEvolutionStrongLimit_zero_apply A hA x

/-- Applying the same varying isometry to a convergent varying vector preserves convergence.  This
is the only extra analytic input needed to pass the approximating group law to the strong limit. -/
private theorem tendsto_resolventApproximationEvolutionAtScale_comp_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t s : ℝ) (x : H) :
    Tendsto
      (fun r : ℝ =>
        resolventApproximationEvolutionAtScale A hA r t
          (resolventApproximationEvolutionAtScale A hA r s x))
      atTop
      (𝓝 (resolventEvolutionStrongLimitOperator A hA t
        (resolventEvolutionStrongLimitOperator A hA s x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hs := (Metric.tendsto_nhds.mp
    (tendsto_resolventApproximationEvolutionAtScale_apply A hA s x)) (ε / 2) hε2
  have ht := (Metric.tendsto_nhds.mp
    (tendsto_resolventApproximationEvolutionAtScale_apply A hA t
      (resolventEvolutionStrongLimitOperator A hA s x))) (ε / 2) hε2
  filter_upwards [hs, ht] with r hrs hrt
  have hrs' :
      dist (resolventApproximationEvolutionAtScale A hA r s x)
          (resolventEvolutionStrongLimitOperator A hA s x) < ε / 2 := by
    simpa using hrs
  have hrt' :
      dist (resolventApproximationEvolutionAtScale A hA r t
          (resolventEvolutionStrongLimitOperator A hA s x))
        (resolventEvolutionStrongLimitOperator A hA t
          (resolventEvolutionStrongLimitOperator A hA s x)) < ε / 2 := by
    simpa using hrt
  have htri := dist_triangle
    (resolventApproximationEvolutionAtScale A hA r t
      (resolventApproximationEvolutionAtScale A hA r s x))
    (resolventApproximationEvolutionAtScale A hA r t
      (resolventEvolutionStrongLimitOperator A hA s x))
    (resolventEvolutionStrongLimitOperator A hA t
      (resolventEvolutionStrongLimitOperator A hA s x))
  have hiso :
      dist
        (resolventApproximationEvolutionAtScale A hA r t
          (resolventApproximationEvolutionAtScale A hA r s x))
        (resolventApproximationEvolutionAtScale A hA r t
          (resolventEvolutionStrongLimitOperator A hA s x)) =
        dist (resolventApproximationEvolutionAtScale A hA r s x)
          (resolventEvolutionStrongLimitOperator A hA s x) :=
    resolventApproximationEvolutionAtScale_dist_eq A hA r t _ _
  rw [hiso] at htri
  exact lt_of_le_of_lt htri (by linarith)

/-- The additive one-parameter group law passes to the vectorwise strong limit. -/
theorem resolventEvolutionStrongLimit_add_time_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t s : ℝ) (x : H) :
    resolventEvolutionStrongLimit A hA (t + s) x =
      resolventEvolutionStrongLimitOperator A hA t
        (resolventEvolutionStrongLimitOperator A hA s x) := by
  have hleft := tendsto_resolventApproximationEvolutionAtScale_apply A hA (t + s) x
  have hright :=
    tendsto_resolventApproximationEvolutionAtScale_comp_apply A hA t s x
  exact tendsto_nhds_unique hleft <|
    hright.congr' (Eventually.of_forall fun r => by
      have hgroup := congrArg (fun T : H →L[ℂ] H => T x)
        (resolventApproximationEvolutionAtScale_add A hA r t s)
      simpa using hgroup.symm)

/-- The bundled strong-limit operators form an additive one-parameter group. -/
theorem resolventEvolutionStrongLimitOperator_add
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t s : ℝ) :
    resolventEvolutionStrongLimitOperator A hA (t + s) =
      resolventEvolutionStrongLimitOperator A hA t *
        resolventEvolutionStrongLimitOperator A hA s := by
  ext x
  simpa using resolventEvolutionStrongLimit_add_time_apply A hA t s x

/-- Negative time is a left inverse. -/
theorem resolventEvolutionStrongLimitOperator_neg_mul
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    resolventEvolutionStrongLimitOperator A hA (-t) *
        resolventEvolutionStrongLimitOperator A hA t = 1 := by
  rw [← resolventEvolutionStrongLimitOperator_add]
  simp

/-- Negative time is a right inverse. -/
theorem resolventEvolutionStrongLimitOperator_mul_neg
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    resolventEvolutionStrongLimitOperator A hA t *
        resolventEvolutionStrongLimitOperator A hA (-t) = 1 := by
  rw [← resolventEvolutionStrongLimitOperator_add]
  simp

/-- The limiting evolution preserves the Hilbert-space inner product. -/
theorem resolventEvolutionStrongLimitOperator_inner_map_map
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x y : H) :
    inner ℂ (resolventEvolutionStrongLimitOperator A hA t x)
        (resolventEvolutionStrongLimitOperator A hA t y) = inner ℂ x y := by
  exact (LinearMap.norm_map_iff_inner_map_map
    (resolventEvolutionStrongLimitOperator A hA t)).mp
      (fun z => by
        simpa using resolventEvolutionStrongLimit_apply_norm A hA t z) x y

/-- The Hilbert-space adjoint of the limiting evolution is negative-time evolution. -/
theorem resolventEvolutionStrongLimitOperator_adjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    ContinuousLinearMap.adjoint (resolventEvolutionStrongLimitOperator A hA t) =
      resolventEvolutionStrongLimitOperator A hA (-t) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hinner := resolventEvolutionStrongLimitOperator_inner_map_map A hA t
    (resolventEvolutionStrongLimitOperator A hA (-t) x) y
  have hcancel :
      resolventEvolutionStrongLimitOperator A hA t
        (resolventEvolutionStrongLimitOperator A hA (-t) x) = x := by
    have happ := congrArg (fun T : H →L[ℂ] H => T x)
      (resolventEvolutionStrongLimitOperator_mul_neg A hA t)
    simpa using happ
  rw [hcancel] at hinner
  exact hinner.symm

/-- Star/adjoint reverses time for the limiting evolution. -/
theorem resolventEvolutionStrongLimitOperator_star
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (resolventEvolutionStrongLimitOperator A hA t) =
      resolventEvolutionStrongLimitOperator A hA (-t) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact resolventEvolutionStrongLimitOperator_adjoint A hA t

/-- The limiting evolution is unitary, left-inverse form. -/
theorem resolventEvolutionStrongLimitOperator_star_mul
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (resolventEvolutionStrongLimitOperator A hA t) *
        resolventEvolutionStrongLimitOperator A hA t = 1 := by
  rw [resolventEvolutionStrongLimitOperator_star]
  exact resolventEvolutionStrongLimitOperator_neg_mul A hA t

/-- The limiting evolution is unitary, right-inverse form. -/
theorem resolventEvolutionStrongLimitOperator_mul_star
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    resolventEvolutionStrongLimitOperator A hA t *
        star (resolventEvolutionStrongLimitOperator A hA t) = 1 := by
  rw [resolventEvolutionStrongLimitOperator_star]
  exact resolventEvolutionStrongLimitOperator_mul_neg A hA t

end

end LinearPMap
