import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionDomain
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Generator of the limiting Stone evolution

This module identifies the infinitesimal generator of the strongly continuous Stone evolution on
the original self-adjoint operator domain and transports the generator equation from zero to
arbitrary time.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A fixed bounded approximating evolution differs from the limiting evolution by at most its
generator error times `|t|`, on the original generator domain. -/
theorem norm_stoneEvolution_sub_resolventApproximationEvolution_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (x : A.domain) :
    ‖stoneEvolution A hA t (x : H) -
        resolventApproximationEvolution A hA r hr t (x : H)‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t| := by
  let Ur : H →L[ℂ] H := resolventApproximationEvolution A hA r hr t
  let Ar : H →L[ℂ] H := boundedSelfAdjointApproximation A hA r hr
  have hU :
      Tendsto
        (fun s : ℝ =>
          ‖Ur (x : H) - resolventApproximationEvolutionAtScale A hA s t (x : H)‖)
        atTop
        (𝓝 ‖Ur (x : H) - stoneEvolution A hA t (x : H)‖) := by
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
      ‖Ur (x : H) - stoneEvolution A hA t (x : H)‖ -
          ‖Ar (x : H) - A x‖ * |t| ≤ 0 := by
    apply le_of_tendsto hdiff
    exact Filter.Eventually.of_forall fun s => by
      have hpair := norm_resolventApproximationEvolution_sub_atScale_le\n        A hA r hr s t (x : H)\n      linarith
  rw [norm_sub_rev]
  linarith

private theorem norm_slope_sub_resolventApproximationEvolution_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ≠ 0) (x : A.domain) :
    ‖t⁻¹ •
          (stoneEvolution A hA t (x : H) - (x : H)) -
        t⁻¹ •
          (resolventApproximationEvolution A hA r hr t (x : H) - (x : H))‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ := by
  have hbound :=
    norm_stoneEvolution_sub_resolventApproximationEvolution_le
      A hA r hr t x
  have hvec :
      (stoneEvolution A hA t (x : H) - (x : H)) -
          (resolventApproximationEvolution A hA r hr t (x : H) - (x : H)) =
        stoneEvolution A hA t (x : H) -
          resolventApproximationEvolution A hA r hr t (x : H) := by
    abel
  rw [← smul_sub, hvec, norm_smul]
  change |t⁻¹| *
      ‖stoneEvolution A hA t (x : H) -
        resolventApproximationEvolution A hA r hr t (x : H)‖ ≤ _
  rw [abs_inv]
  calc
    |t|⁻¹ *
        ‖stoneEvolution A hA t (x : H) -
          resolventApproximationEvolution A hA r hr t (x : H)‖
        ≤ |t|⁻¹ *
            (‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t|) := by
          exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (abs_nonneg t))
    _ = ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ := by
      field_simp [abs_ne_zero.mpr ht]

/-- At zero time, the strong Stone evolution has infinitesimal generator `-i A` on `A.domain`. -/
theorem stoneEvolution_apply_hasDerivAt_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    HasDerivAt (fun t : ℝ => stoneEvolution A hA t (x : H))
      ((-I : ℂ) • A x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add]
  have hzero :
      stoneEvolution A hA 0 (x : H) = (x : H) := by
    have h := congrArg (fun T : H →L[ℂ] H => T (x : H))
      (stoneEvolution_zero A hA)
    simpa using h
  rw [hzero]
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
    have hvalue :
        ((resolventApproximationEvolution A hA r hr 0 *
            ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr)) (x : H)) =
          ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H)) := by
      rw [resolventApproximationEvolution_zero, one_mul]
      rfl
    rw [hvalue] at h
    exact h
  have hslope := hderiv.tendsto_slope_zero
  have happ := (Metric.tendsto_nhds.mp hslope) (ε / 3) hε3
  filter_upwards [happ, self_mem_nhdsWithin] with t htapp htmem
  have ht : t ≠ 0 := by
    simpa using htmem
  have hfirst :=
    norm_slope_sub_resolventApproximationEvolution_le A hA r hr t ht x
  have hfirst' :
      dist
          (t⁻¹ • (stoneEvolution A hA t (x : H) - (x : H)))
          (t⁻¹ • (resolventApproximationEvolution A hA r hr t (x : H) - (x : H))) <
        ε / 3 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hfirst hgen
  have hsecond :
      dist
          (t⁻¹ • (resolventApproximationEvolution A hA r hr t (x : H) - (x : H)))
          ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H)) <
        ε / 3 := by
    have hzero_r :
        resolventApproximationEvolution A hA r hr 0 (x : H) = (x : H) := by
      have h := congrArg (fun T : H →L[ℂ] H => T (x : H))
        (resolventApproximationEvolution_zero A hA r hr)
      simpa using h
    simpa [hzero_r] using htapp
  have hthird :
      dist ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H))
          ((-I : ℂ) • A x) < ε / 3 := by
    rw [dist_eq_norm, ← smul_sub, norm_smul]
    simpa using hgen
  have htri := dist_triangle4
    (t⁻¹ • (stoneEvolution A hA t (x : H) - (x : H)))
    (t⁻¹ • (resolventApproximationEvolution A hA r hr t (x : H) - (x : H)))
    ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H))
    ((-I : ℂ) • A x)
  exact lt_of_le_of_lt htri (by linarith)

/-- The limiting evolution satisfies its strong generator equation at arbitrary time, with the
right-hand side written as the evolved generator. -/
private theorem stoneEvolution_apply_hasDerivAt_intertwined
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ => stoneEvolution A hA t (x : H))
      ((-I : ℂ) • stoneEvolution A hA s (A x)) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hzero :=
    (stoneEvolution_apply_hasDerivAt_zero A hA x).tendsto_slope_zero
  have hmapped :
      Tendsto
        (fun h : ℝ =>
          stoneEvolution A hA s
            (h⁻¹ •
              (stoneEvolution A hA (0 + h) (x : H) -
                stoneEvolution A hA 0 (x : H))))
        (𝓝[≠] 0)
        (𝓝 (stoneEvolution A hA s ((-I : ℂ) • A x))) := by
    exact ((stoneEvolution A hA s).continuous.tendsto _).comp hzero
  have hfun :
      (fun h : ℝ =>
        h⁻¹ •
          (stoneEvolution A hA (s + h) (x : H) -
            stoneEvolution A hA s (x : H))) =
      (fun h : ℝ =>
        stoneEvolution A hA s
          (h⁻¹ •
            (stoneEvolution A hA (0 + h) (x : H) -
              stoneEvolution A hA 0 (x : H)))) := by
    funext h
    rw [show
      stoneEvolution A hA (s + h) (x : H) =
        stoneEvolution A hA s
          (stoneEvolution A hA h (x : H)) by
      simpa only [stoneEvolution_apply] using
        resolventEvolutionStrongLimit_add_time_apply A hA s h (x : H)]
    rw [show stoneEvolution A hA 0 (x : H) = (x : H) by
      simpa only [stoneEvolution_apply] using
        resolventEvolutionStrongLimit_zero_apply A hA (x : H)]
    simp only [zero_add]
    rw [← (stoneEvolution A hA s).map_sub]
    symm
    exact (stoneEvolution A hA s).toLinearMap.map_smul_of_tower
      h⁻¹ (stoneEvolution A hA h (x : H) - (x : H))
  rw [hfun]
  have hmapgen :
      stoneEvolution A hA s ((-I : ℂ) • A x) =
        (-I : ℂ) • stoneEvolution A hA s (A x) := by
    exact (stoneEvolution A hA s).map_smul _ _
  rw [hmapgen] at hmapped
  exact hmapped

/-- Strong Stone derivative on the preserved generator domain. -/
theorem stoneEvolution_apply_hasDerivAt
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stoneEvolution A hA s (x : H))
      ((-I : ℂ) •
        A ⟨stoneEvolution A hA t (x : H),
          stoneEvolution_mem_domain A hA t x⟩) t := by
  have h := stoneEvolution_apply_hasDerivAt_intertwined A hA x t
  rw [stoneEvolution_apply_domain A hA t x]
  exact h

end

end LinearPMap
