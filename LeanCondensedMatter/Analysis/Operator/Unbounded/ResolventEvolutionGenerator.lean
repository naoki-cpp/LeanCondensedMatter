import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionDomain
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Generator of the limiting Stone evolution

This module identifies the infinitesimal generator of the strongly continuous Stone evolution on
the original self-adjoint operator domain.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def generatorApproximationScale (r : ℝ) : ℝ := max 1 r

private theorem generatorApproximationScale_pos (r : ℝ) :
    0 < generatorApproximationScale r := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 r)

private noncomputable def boundedSelfAdjointApproximationAtScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) : H →L[ℂ] H :=
  boundedSelfAdjointApproximation A hA (generatorApproximationScale r)
    (generatorApproximationScale_pos r)

private theorem boundedSelfAdjointApproximationAtScale_apply_tendsto
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun r : ℝ => boundedSelfAdjointApproximationAtScale A hA r (x : H))
      atTop (𝓝 (A x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR, hconv⟩ :=
    boundedSelfAdjointApproximation_strong_convergence A hA x ε hε
  filter_upwards [eventually_ge_atTop (max R 1)] with r hr
  have hRr : R ≤ r := (le_max_left R 1).trans hr
  have h1r : 1 ≤ r := (le_max_right R 1).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le h1r
  have h := hconv r hRr hrpos
  simpa [boundedSelfAdjointApproximationAtScale, generatorApproximationScale,
    max_eq_right h1r, dist_eq_norm] using h

private theorem resolventApproximationEvolutionAtScale_eq_generatorScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) :
    resolventApproximationEvolutionAtScale A hA r t =
      resolventApproximationEvolution A hA (generatorApproximationScale r)
        (generatorApproximationScale_pos r) t := by
  rfl

/-- A fixed bounded approximating evolution differs from the limiting evolution by at most its
generator error times `|t|`, on the original generator domain. -/
theorem norm_resolventEvolutionStrongLimitOperator_sub_resolventApproximationEvolution_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (x : A.domain) :
    ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
        resolventApproximationEvolution A hA r hr t (x : H)‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t| := by
  let Ur : H →L[ℂ] H := resolventApproximationEvolution A hA r hr t
  let Ar : H →L[ℂ] H := boundedSelfAdjointApproximation A hA r hr
  have hU :
      Tendsto
        (fun s : ℝ =>
          ‖Ur (x : H) - resolventApproximationEvolutionAtScale A hA s t (x : H)‖)
        atTop
        (𝓝 ‖Ur (x : H) - resolventEvolutionStrongLimitOperator A hA t (x : H)‖) := by
    exact (tendsto_const_nhds.sub
      (tendsto_resolventApproximationEvolutionAtScale_apply A hA t (x : H))).norm
  have hAconv :
      Tendsto
        (fun s : ℝ => boundedSelfAdjointApproximationAtScale A hA s (x : H))
        atTop (𝓝 (A x)) :=
    boundedSelfAdjointApproximationAtScale_apply_tendsto A hA x
  have hgen :
      Tendsto
        (fun s : ℝ =>
          ‖Ar (x : H) - boundedSelfAdjointApproximationAtScale A hA s (x : H)‖ * |t|)
        atTop
        (𝓝 (‖Ar (x : H) - A x‖ * |t|)) := by
    exact (tendsto_const_nhds.sub hAconv).norm.mul_const |t|
  have hdiff := hU.sub hgen
  have hle :
      ‖Ur (x : H) - resolventEvolutionStrongLimitOperator A hA t (x : H)‖ -
          ‖Ar (x : H) - A x‖ * |t| ≤ 0 := by
    apply le_of_tendsto hdiff
    exact Filter.Eventually.of_forall fun s => by
      have hs := generatorApproximationScale_pos s
      have hpair := norm_resolventApproximationEvolution_sub_le
        A hA r (generatorApproximationScale s) hr hs t (x : H)
      have hpair' :
          ‖Ur (x : H) - resolventApproximationEvolutionAtScale A hA s t (x : H)‖ ≤
            ‖Ar (x : H) - boundedSelfAdjointApproximationAtScale A hA s (x : H)‖ * |t| := by
        simpa [Ur, Ar, boundedSelfAdjointApproximationAtScale,
          resolventApproximationEvolutionAtScale_eq_generatorScale A hA s t] using hpair
      linarith
  rw [norm_sub_rev]
  linarith

private theorem norm_slope_sub_resolventApproximationEvolution_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ≠ 0) (x : A.domain) :
    ‖t⁻¹ •
          (resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H)) -
        t⁻¹ •
          (resolventApproximationEvolution A hA r hr t (x : H) - (x : H))‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ := by
  have hbound :=
    norm_resolventEvolutionStrongLimitOperator_sub_resolventApproximationEvolution_le
      A hA r hr t x
  have hvec :
      (resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H)) -
          (resolventApproximationEvolution A hA r hr t (x : H) - (x : H)) =
        resolventEvolutionStrongLimitOperator A hA t (x : H) -
          resolventApproximationEvolution A hA r hr t (x : H) := by
    abel
  rw [← smul_sub, hvec, norm_smul]
  change |t⁻¹| *
      ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
        resolventApproximationEvolution A hA r hr t (x : H)‖ ≤ _
  rw [abs_inv]
  calc
    |t|⁻¹ *
        ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
          resolventApproximationEvolution A hA r hr t (x : H)‖
        ≤ |t|⁻¹ *
            (‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t|) := by
          exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (abs_nonneg t))
    _ = ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ := by
      field_simp [abs_ne_zero.mpr ht]

/-- At zero time, the strong Stone evolution has infinitesimal generator `-i A` on `A.domain`. -/
theorem resolventEvolutionStrongLimitOperator_apply_hasDerivAt_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    HasDerivAt (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t (x : H))
      ((-I : ℂ) • A x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨r, hr, hconv⟩ :=
    boundedSelfAdjointApproximation_strong_convergence A hA x (ε / 3) hε3
  have hgen :
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ < ε / 3 :=
    hconv r le_rfl hr
  have hderiv :
      HasDerivAt
        (fun t : ℝ => resolventApproximationEvolution A hA r hr t (x : H))
        ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H)) 0 := by
    have h := resolventApproximationEvolution_apply_hasDerivAt A hA r hr 0 (x : H)
    simpa [resolventApproximationEvolution_zero] using h
  have hslope := hderiv.tendsto_slope_zero
  have happ := (Metric.tendsto_nhds.mp hslope) (ε / 3) hε3
  filter_upwards [happ, self_mem_nhdsWithin] with t htapp htmem
  have ht : t ≠ 0 := by
    simpa using htmem
  have hfirst :=
    norm_slope_sub_resolventApproximationEvolution_le A hA r hr t ht x
  have hfirst' :
      dist
          (t⁻¹ • (resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H)))
          (t⁻¹ • (resolventApproximationEvolution A hA r hr t (x : H) - (x : H))) <
        ε / 3 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hfirst hgen
  have hsecond :
      dist
          (t⁻¹ • (resolventApproximationEvolution A hA r hr t (x : H) - (x : H)))
          ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H)) <
        ε / 3 := by
    simpa [resolventApproximationEvolution_zero] using htapp
  have hthird :
      dist ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H))
          ((-I : ℂ) • A x) < ε / 3 := by
    rw [dist_eq_norm, ← smul_sub, norm_smul]
    simpa using hgen
  have htri := dist_triangle4
    (t⁻¹ • (resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H)))
    (t⁻¹ • (resolventApproximationEvolution A hA r hr t (x : H) - (x : H)))
    ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H))
    ((-I : ℂ) • A x)
  exact lt_of_le_of_lt htri (by linarith)

end

end LinearPMap
