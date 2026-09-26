import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionCauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Strong limits of the bounded Stone evolutions

The resolvent-approximating unitary evolutions are already strongly Cauchy on the domain of the
original self-adjoint operator.  Since every self-adjoint `LinearPMap` has dense domain and every
bounded approximating evolution is an isometry, the Cauchy estimate extends to every vector in the
Hilbert space.

After clipping the regularization scale below by `1`, the approximants form a `CauchySeq` indexed
by `ℝ` at `+∞`.  Completeness of the Hilbert space then gives a canonical vectorwise strong limit
via `Filter.limUnder`.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded self-adjoint evolution preserves distances. -/
theorem boundedUnitaryEvolution_dist_eq
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (t : ℝ) (x y : H) :
    dist (boundedUnitaryEvolution B t x) (boundedUnitaryEvolution B t y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← (boundedUnitaryEvolution B t).map_sub]
  exact boundedUnitaryEvolution_apply_norm B hB t (x - y)

/-- Each resolvent-approximating unitary evolution is an isometry. -/
theorem resolventApproximationEvolution_dist_eq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (x y : H) :
    dist (resolventApproximationEvolution A hA r hr t x)
        (resolventApproximationEvolution A hA r hr t y) = dist x y := by
  simpa [resolventApproximationEvolution] using
    boundedUnitaryEvolution_dist_eq
      (boundedSelfAdjointApproximation A hA r hr)
      (boundedSelfAdjointApproximation_isSelfAdjoint A hA r hr) t x y

/-- A family of isometries that is pointwise Cauchy on a dense set is pointwise Cauchy
everywhere. -/
theorem cauchySeq_apply_of_isometry_of_dense
    {ι X Y : Type*} [Nonempty ι] [SemilatticeSup ι]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ι → X → Y) {s : Set X} (hs : Dense s)
    (hF : ∀ i, Isometry (F i))
    (hcauchy : ∀ x ∈ s, CauchySeq (fun i => F i x)) :
    ∀ x, CauchySeq (fun i => F i x) := by
  intro x
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨y, hys, hxy⟩ := hs.exists_dist_lt x hε3
  obtain ⟨i₀, hi₀⟩ := Metric.cauchySeq_iff.1 (hcauchy y hys) (ε / 3) hε3
  refine ⟨i₀, ?_⟩
  intro i hi j hj
  have hleft : dist (F i x) (F i y) < ε / 3 := by
    rw [(hF i).dist_eq]
    exact hxy
  have hmid : dist (F i y) (F j y) < ε / 3 := hi₀ i hi j hj
  have hright : dist (F j y) (F j x) < ε / 3 := by
    rw [(hF j).dist_eq, dist_comm]
    exact hxy
  calc
    dist (F i x) (F j x) ≤
        dist (F i x) (F i y) + (dist (F i y) (F j y) + dist (F j y) (F j x)) := by
      calc
        dist (F i x) (F j x) ≤
            dist (F i x) (F i y) + dist (F i y) (F j x) := dist_triangle _ _ _
        _ ≤ dist (F i x) (F i y) +
            (dist (F i y) (F j y) + dist (F j y) (F j x)) := by
          gcongr
          exact dist_triangle _ _ _
    _ < ε := by linarith

/-- For every fixed time and vector, the totalized resolvent approximations are a Cauchy sequence
as the real scale tends to positive infinity. -/
theorem resolventApproximationEvolutionAtScale_apply_cauchySeq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    CauchySeq (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x) := by
  apply cauchySeq_apply_of_isometry_of_dense
    (fun r y => resolventApproximationEvolutionAtScale A hA r t y)
    hA.dense_domain
  · intro r
    rw [isometry_iff_dist_eq]
    intro y z
    unfold resolventApproximationEvolutionAtScale
    exact resolventApproximationEvolution_dist_eq A hA _ _ t y z
  · intro y hy
    exact resolventApproximationEvolutionAtScale_apply_domain_cauchySeq
      A hA t ⟨y, hy⟩

/-- The vectorwise strong limit of the resolvent-approximating unitary evolutions. -/
noncomputable def resolventEvolutionStrongLimit
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) : H :=
  limUnder atTop (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x)

/-- The totalized resolvent approximations converge strongly to `resolventEvolutionStrongLimit`. -/
theorem tendsto_resolventApproximationEvolutionAtScale_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    Tendsto (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x)
      atTop (𝓝 (resolventEvolutionStrongLimit A hA t x)) := by
  simpa [resolventEvolutionStrongLimit] using
    (resolventApproximationEvolutionAtScale_apply_cauchySeq A hA t x).tendsto_limUnder

end

end LinearPMap
