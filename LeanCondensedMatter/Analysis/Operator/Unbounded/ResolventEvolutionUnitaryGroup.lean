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
        have happ := congrArg (fun T : H →L[ℂ] H => T x)
          (resolventApproximationEvolutionAtScale_zero A hA r)
        simpa using happ.symm)

/-- The bundled strong-limit evolution is the identity at time zero. -/
@[simp]
theorem stoneEvolution_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    stoneEvolution A hA 0 = 1 := by
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
      (𝓝 (stoneEvolution A hA t
        (stoneEvolution A hA s x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hs := (Metric.tendsto_nhds.mp
    (tendsto_resolventApproximationEvolutionAtScale_apply A hA s x)) (ε / 2) hε2
  have ht := (Metric.tendsto_nhds.mp
    (tendsto_resolventApproximationEvolutionAtScale_apply A hA t
      (stoneEvolution A hA s x))) (ε / 2) hε2
  filter_upwards [hs, ht] with r hrs hrt
  have hrs' :
      dist (resolventApproximationEvolutionAtScale A hA r s x)
          (stoneEvolution A hA s x) < ε / 2 := by
    simpa using hrs
  have hrt' :
      dist (resolventApproximationEvolutionAtScale A hA r t
          (stoneEvolution A hA s x))
        (stoneEvolution A hA t
          (stoneEvolution A hA s x)) < ε / 2 := by
    simpa using hrt
  have htri := dist_triangle
    (resolventApproximationEvolutionAtScale A hA r t
      (resolventApproximationEvolutionAtScale A hA r s x))
    (resolventApproximationEvolutionAtScale A hA r t
      (stoneEvolution A hA s x))
    (stoneEvolution A hA t
      (stoneEvolution A hA s x))
  have hiso :
      dist
        (resolventApproximationEvolutionAtScale A hA r t
          (resolventApproximationEvolutionAtScale A hA r s x))
        (resolventApproximationEvolutionAtScale A hA r t
          (stoneEvolution A hA s x)) =
        dist (resolventApproximationEvolutionAtScale A hA r s x)
          (stoneEvolution A hA s x) :=
    resolventApproximationEvolutionAtScale_dist_eq A hA r t _ _
  rw [hiso] at htri
  exact lt_of_le_of_lt htri (by linarith)

/-- The additive one-parameter group law passes to the vectorwise strong limit. -/
theorem resolventEvolutionStrongLimit_add_time_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t s : ℝ) (x : H) :
    resolventEvolutionStrongLimit A hA (t + s) x =
      stoneEvolution A hA t
        (stoneEvolution A hA s x) := by
  have hleft := tendsto_resolventApproximationEvolutionAtScale_apply A hA (t + s) x
  have hright :=
    tendsto_resolventApproximationEvolutionAtScale_comp_apply A hA t s x
  exact tendsto_nhds_unique hleft <|
    hright.congr' (Eventually.of_forall fun r => by
      have hgroup :
          resolventApproximationEvolutionAtScale A hA r (t + s) =
            resolventApproximationEvolutionAtScale A hA r t *
              resolventApproximationEvolutionAtScale A hA r s := by
        unfold resolventApproximationEvolutionAtScale
        exact resolventApproximationEvolution_add A hA _ _ t s
      simpa using
        (congrArg (fun T : H →L[ℂ] H => T x) hgroup).symm)

/-- The bundled strong-limit operators form an additive one-parameter group. -/
theorem stoneEvolution_add
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t s : ℝ) :
    stoneEvolution A hA (t + s) =
      stoneEvolution A hA t *
        stoneEvolution A hA s := by
  ext x
  simpa using resolventEvolutionStrongLimit_add_time_apply A hA t s x

/-- Negative time is a left inverse. -/
theorem stoneEvolution_neg_mul
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneEvolution A hA (-t) *
        stoneEvolution A hA t = 1 := by
  rw [← stoneEvolution_add]
  simp

/-- Negative time is a right inverse. -/
theorem stoneEvolution_mul_neg
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneEvolution A hA t *
        stoneEvolution A hA (-t) = 1 := by
  rw [← stoneEvolution_add]
  simp

/-- The limiting evolution preserves the Hilbert-space inner product. -/
theorem stoneEvolution_inner_map_map
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x y : H) :
    inner ℂ (stoneEvolution A hA t x)
        (stoneEvolution A hA t y) = inner ℂ x y := by
  exact (LinearMap.norm_map_iff_inner_map_map
    (stoneEvolution A hA t)).mp
      (fun z => by
        simpa using resolventEvolutionStrongLimit_apply_norm A hA t z) x y

/-- Star/adjoint reverses time for the limiting evolution. -/
theorem stoneEvolution_star
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (stoneEvolution A hA t) =
      stoneEvolution A hA (-t) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hinner := stoneEvolution_inner_map_map A hA t
    (stoneEvolution A hA (-t) x) y
  have hcancel :
      stoneEvolution A hA t
        (stoneEvolution A hA (-t) x) = x := by
    simpa only [stoneEvolution_apply, add_neg_cancel,
      resolventEvolutionStrongLimit_zero_apply] using
      (resolventEvolutionStrongLimit_add_time_apply A hA t (-t) x).symm
  rw [hcancel] at hinner
  exact hinner.symm

/-- The limiting evolution is unitary, left-inverse form. -/
theorem stoneEvolution_star_mul
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (stoneEvolution A hA t) *
        stoneEvolution A hA t = 1 := by
  rw [stoneEvolution_star]
  exact stoneEvolution_neg_mul A hA t

/-- The limiting evolution is unitary, right-inverse form. -/
theorem stoneEvolution_mul_star
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneEvolution A hA t *
        star (stoneEvolution A hA t) = 1 := by
  rw [stoneEvolution_star]
  exact stoneEvolution_mul_neg A hA t

end

end LinearPMap
