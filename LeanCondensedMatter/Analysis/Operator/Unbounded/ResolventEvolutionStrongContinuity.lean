import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionUnitaryGroup
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Strong continuity of the limiting Stone evolution

The bounded resolvent evolutions satisfy the displacement estimate
`‖Uᵣ(t)x - x‖ ≤ ‖Aᵣ x‖ |t|`.  On the original domain, the resolvent regularizer representation of
`Aᵣ` improves this uniformly to `‖Uᵣ(t)x - x‖ ≤ ‖A x‖ |t|`.  Passing to the vectorwise strong
limit gives continuity at zero on the generator domain.  Density of the self-adjoint domain and
unitarity extend continuity at zero to every vector, and the group law transports it to every time.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On the original generator domain, every totalized bounded approximant has displacement bounded
uniformly in the approximation scale by the original generator. -/
theorem norm_resolventApproximationEvolutionAtScale_apply_sub_le_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) (x : A.domain) :
    ‖resolventApproximationEvolutionAtScale A hA r t (x : H) - (x : H)‖ ≤
      ‖A x‖ * |t| := by
  unfold resolventApproximationEvolutionAtScale resolventApproximationEvolution
  calc
    ‖boundedUnitaryEvolution (boundedSelfAdjointApproximation A hA _ _) t (x : H) - (x : H)‖
        ≤ ‖boundedSelfAdjointApproximation A hA _ _ (x : H)‖ * |t| :=
          norm_boundedUnitaryEvolution_apply_sub_le
            (boundedSelfAdjointApproximation A hA _ _)
            (boundedSelfAdjointApproximation_isSelfAdjoint A hA _ _) t (x : H)
    _ = ‖resolventRegularizer A hA _ _ (A x)‖ * |t| := by
      rw [boundedSelfAdjointApproximation_apply_domain A hA _ _ x]
    _ ≤ ‖A x‖ * |t| := by
      gcongr
      exact norm_resolventRegularizer_le A hA _ _ (A x)

/-- The limiting Stone evolution inherits the domain displacement estimate
`‖U(t)x - x‖ ≤ ‖A x‖ |t|`. -/
theorem norm_resolventEvolutionStrongLimitOperator_apply_sub_le_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H)‖ ≤
      ‖A x‖ * |t| := by
  have hconv :
      Tendsto
        (fun r : ℝ =>
          ‖resolventApproximationEvolutionAtScale A hA r t (x : H) - (x : H)‖)
        atTop
        (𝓝 ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H)‖) := by
    simpa using
      ((tendsto_resolventApproximationEvolutionAtScale_apply A hA t (x : H)).sub_const
        (x : H)).norm
  exact le_of_tendsto hconv <|
    Filter.Eventually.of_forall fun r =>
      norm_resolventApproximationEvolutionAtScale_apply_sub_le_domain A hA r t x

/-- For a vector in the generator domain, the limiting evolution is continuous at time zero. -/
theorem resolventEvolutionStrongLimitOperator_apply_continuousAt_zero_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    ContinuousAt (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t (x : H)) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let M : ℝ := ‖A x‖
  let δ : ℝ := ε / (M + 1)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hden : 0 < M + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have ht' : |t| < δ := by
    simpa [Real.dist_eq] using ht
  have hprod : M * |t| < ε := by
    have hle : M * |t| ≤ M * δ :=
      mul_le_mul_of_nonneg_left (le_of_lt ht') hM
    have hfrac : M / (M + 1) < 1 :=
      (div_lt_one hden).2 (by linarith)
    have hMδ : M * δ < ε := by
      calc
        M * δ = ε * (M / (M + 1)) := by
          dsimp [δ]
          ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := by ring
    exact lt_of_le_of_lt hle hMδ
  rw [resolventEvolutionStrongLimitOperator_zero]
  change dist (resolventEvolutionStrongLimitOperator A hA t (x : H)) (x : H) < ε
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    (norm_resolventEvolutionStrongLimitOperator_apply_sub_le_domain A hA t x) hprod

/-- The limiting evolution is continuous at time zero on every Hilbert-space vector. -/
theorem resolventEvolutionStrongLimitOperator_apply_continuousAt_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (y : H) :
    ContinuousAt (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t y) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨x, hxA, hyx⟩ := hA.dense_domain.exists_dist_lt y hε4
  let xA : A.domain := ⟨x, hxA⟩
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hxcont⟩ :=
    (Metric.continuousAt_iff.mp
      (resolventEvolutionStrongLimitOperator_apply_continuousAt_zero_domain A hA xA))
      (ε / 2) hε2
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hmid := hxcont ht
  have hleft :
      dist (resolventEvolutionStrongLimitOperator A hA t y)
          (resolventEvolutionStrongLimitOperator A hA t x) = dist y x :=
    resolventEvolutionStrongLimitOperator_dist_eq A hA t y x
  have hright :
      dist (resolventEvolutionStrongLimitOperator A hA 0 x)
          (resolventEvolutionStrongLimitOperator A hA 0 y) = dist x y :=
    resolventEvolutionStrongLimitOperator_dist_eq A hA 0 x y
  have hxy : dist x y < ε / 4 := by
    simpa [dist_comm] using hyx
  have htri := dist_triangle4
    (resolventEvolutionStrongLimitOperator A hA t y)
    (resolventEvolutionStrongLimitOperator A hA t x)
    (resolventEvolutionStrongLimitOperator A hA 0 x)
    (resolventEvolutionStrongLimitOperator A hA 0 y)
  rw [hleft, hright] at htri
  exact lt_of_le_of_lt htri (by linarith)

/-- Time differences for the limiting unitary group reduce isometrically to a displacement from
zero time. -/
theorem resolventEvolutionStrongLimitOperator_dist_time_eq_sub
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t s : ℝ) (x : H) :
    dist (resolventEvolutionStrongLimitOperator A hA t x)
        (resolventEvolutionStrongLimitOperator A hA s x) =
      dist (resolventEvolutionStrongLimitOperator A hA (t - s) x) x := by
  rw [show
    resolventEvolutionStrongLimitOperator A hA t x =
      resolventEvolutionStrongLimitOperator A hA s
        (resolventEvolutionStrongLimitOperator A hA (t - s) x) by
    simpa only [resolventEvolutionStrongLimitOperator_apply,
      show s + (t - s) = t by ring] using
      resolventEvolutionStrongLimit_add_time_apply A hA s (t - s) x]
  exact resolventEvolutionStrongLimitOperator_dist_eq A hA s _ x

/-- The limiting evolution is strongly continuous at every time, for every vector. -/
theorem resolventEvolutionStrongLimitOperator_apply_continuousAt
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : H) (s : ℝ) :
    ContinuousAt (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t x) s := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hzero⟩ :=
    (Metric.continuousAt_iff.mp
      (resolventEvolutionStrongLimitOperator_apply_continuousAt_zero A hA x)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hshift : dist (t - s) 0 < δ := by
    simpa [Real.dist_eq] using ht
  have hz := hzero hshift
  rw [resolventEvolutionStrongLimitOperator_dist_time_eq_sub A hA t s x]
  simpa using hz

/-- The limiting unitary group is strongly continuous: every orbit `t ↦ U(t)x` is continuous. -/
theorem resolventEvolutionStrongLimitOperator_apply_continuous
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    Continuous (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t x) := by
  rw [continuous_iff_continuousAt]
  exact resolventEvolutionStrongLimitOperator_apply_continuousAt A hA x

end

end LinearPMap
