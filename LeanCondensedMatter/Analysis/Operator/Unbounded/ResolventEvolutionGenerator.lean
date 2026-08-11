import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionDomain
import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedUnitaryEvolutionVectorwise
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Generator of the limiting Stone evolution

The bounded resolvent evolutions already satisfy their bounded-generator differential equations.
The strong-limit construction also gives a quantitative Cauchy estimate.  Passing one approximation
scale to infinity yields the domain estimate

`‖Uᵣ(t)x - U(t)x‖ ≤ ‖Aᵣ x - A x‖ |t|`.

This estimate is strong enough to identify the derivative of the limiting group at zero without
introducing an integration layer: first choose `r` so that `Aᵣ x` is close to `A x`, then use the
bounded derivative theorem for `Uᵣ`.  The group law transports the zero-time derivative to every
time, and domain intertwining identifies the result with `-i A(U(t)x)`.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def generatorApproximationScale (r : ℝ) : ℝ :=
  max 1 r

private theorem generatorApproximationScale_pos (r : ℝ) :
    0 < generatorApproximationScale r := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 r)

private theorem resolventApproximationEvolutionAtScale_eq_generatorApproximationScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) :
    resolventApproximationEvolutionAtScale A hA r t =
      resolventApproximationEvolution A hA (generatorApproximationScale r)
        (generatorApproximationScale_pos r) t := by
  rfl

private theorem tendsto_boundedSelfAdjointApproximation_generatorScale_apply_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto
      (fun r : ℝ =>
        boundedSelfAdjointApproximation A hA (generatorApproximationScale r)
          (generatorApproximationScale_pos r) (x : H))
      atTop (𝓝 (A x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR, hconv⟩ :=
    boundedSelfAdjointApproximation_strong_convergence A hA x ε hε
  filter_upwards [eventually_ge_atTop (max R 1)] with r hr
  have hRr : R ≤ r := (le_max_left R 1).trans hr
  have hRscale : R ≤ generatorApproximationScale r :=
    hRr.trans (le_max_right 1 r)
  simpa [dist_eq_norm] using
    hconv (generatorApproximationScale r) hRscale (generatorApproximationScale_pos r)

/-- A fixed bounded resolvent evolution approaches the limiting Stone evolution on the original
operator domain with an error that is linear in time and controlled only by the generator error. -/
theorem norm_resolventApproximationEvolution_apply_sub_strongLimit_le_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (x : A.domain) :
    ‖resolventApproximationEvolution A hA r hr t (x : H) -
        resolventEvolutionStrongLimitOperator A hA t (x : H)‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t| := by
  let Ar : H →L[ℂ] H := boundedSelfAdjointApproximation A hA r hr
  have hleft :
      Tendsto
        (fun s : ℝ =>
          ‖resolventApproximationEvolution A hA r hr t (x : H) -
            resolventApproximationEvolutionAtScale A hA s t (x : H)‖)
        atTop
        (𝓝 ‖resolventApproximationEvolution A hA r hr t (x : H) -
          resolventEvolutionStrongLimitOperator A hA t (x : H)‖) := by
    simpa using
      (tendsto_const_nhds.sub
        (tendsto_resolventApproximationEvolutionAtScale_apply A hA t (x : H))).norm
  have hgen :=
    tendsto_boundedSelfAdjointApproximation_generatorScale_apply_domain A hA x
  have hright :
      Tendsto
        (fun s : ℝ =>
          ‖Ar (x : H) -
            boundedSelfAdjointApproximation A hA (generatorApproximationScale s)
              (generatorApproximationScale_pos s) (x : H)‖ * |t|)
        atTop
        (𝓝 (‖Ar (x : H) - A x‖ * |t|)) := by
    exact (tendsto_const_nhds.sub hgen).norm.mul_const |t|
  have hle :
      ∀ᶠ s : ℝ in atTop,
        ‖resolventApproximationEvolution A hA r hr t (x : H) -
            resolventApproximationEvolutionAtScale A hA s t (x : H)‖ ≤
          ‖Ar (x : H) -
            boundedSelfAdjointApproximation A hA (generatorApproximationScale s)
              (generatorApproximationScale_pos s) (x : H)‖ * |t| := by
    filter_upwards with s
    rw [resolventApproximationEvolutionAtScale_eq_generatorApproximationScale]
    simpa [Ar] using
      norm_resolventApproximationEvolution_sub_le A hA r
        (generatorApproximationScale s) hr (generatorApproximationScale_pos s) t (x : H)
  exact le_of_tendsto_of_tendsto hleft hright hle

/-- At zero time, the limiting Stone evolution has infinitesimal generator `-i A` on the original
self-adjoint operator domain. -/
theorem resolventEvolutionStrongLimitOperator_apply_hasDerivAt_zero_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    HasDerivAt
      (fun t : ℝ => resolventEvolutionStrongLimitOperator A hA t (x : H))
      ((-I : ℂ) • A x) 0 := by
  rw [hasDerivAt_iff_tendsto, Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨R, hR, hconv⟩ :=
    boundedSelfAdjointApproximation_strong_convergence A hA x (ε / 4) hε4
  let r : ℝ := max R 1
  have hr : 0 < r := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hRr : R ≤ r := le_max_left R 1
  let Ar : H →L[ℂ] H := boundedSelfAdjointApproximation A hA r hr
  have hgen : ‖Ar (x : H) - A x‖ < ε / 4 := by
    simpa [Ar] using hconv r hRr hr
  have hUr :
      HasDerivAt
        (fun t : ℝ => resolventApproximationEvolution A hA r hr t (x : H))
        ((-I : ℂ) • Ar (x : H)) 0 := by
    change HasDerivAt
      (fun t : ℝ => resolventApproximationEvolution A hA r hr t (x : H))
      ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr (x : H)) 0
    simpa [resolventApproximationEvolution_zero] using
      resolventApproximationEvolution_apply_hasDerivAt A hA r hr 0 (x : H)
  have hsmall0 :=
    (Metric.tendsto_nhds.mp (hasDerivAt_iff_tendsto.mp hUr)) (ε / 2) (by positivity)
  have hsmall :
      ∀ᶠ t : ℝ in 𝓝 0,
        ‖t - 0‖⁻¹ *
            ‖resolventApproximationEvolution A hA r hr t (x : H) -
              resolventApproximationEvolution A hA r hr 0 (x : H) -
              (t - 0) • ((-I : ℂ) • Ar (x : H))‖ < ε / 2 := by
    filter_upwards [hsmall0] with t ht
    have hnonneg :
        0 ≤ ‖t - 0‖⁻¹ *
          ‖resolventApproximationEvolution A hA r hr t (x : H) -
            resolventApproximationEvolution A hA r hr 0 (x : H) -
            (t - 0) • ((-I : ℂ) • Ar (x : H))‖ :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using ht
  filter_upwards [hsmall] with t ht
  by_cases ht0 : t = 0
  · subst t
    simpa using hε
  · have habs_ne : |t| ≠ 0 := abs_ne_zero.mpr ht0
    have hinv_nonneg : 0 ≤ ‖t‖⁻¹ := inv_nonneg.mpr (norm_nonneg t)
    have happrox :=
      norm_resolventApproximationEvolution_apply_sub_strongLimit_le_domain
        A hA r hr t x
    have hfirstRaw :
        ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
            resolventApproximationEvolution A hA r hr t (x : H)‖ ≤
          ‖Ar (x : H) - A x‖ * |t| := by
      simpa [Ar, norm_sub_rev] using happrox
    have hfirst :
        ‖t‖⁻¹ *
            ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
              resolventApproximationEvolution A hA r hr t (x : H)‖ ≤
          ‖Ar (x : H) - A x‖ := by
      calc
        ‖t‖⁻¹ *
            ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
              resolventApproximationEvolution A hA r hr t (x : H)‖ ≤
            ‖t‖⁻¹ * (‖Ar (x : H) - A x‖ * |t|) :=
          mul_le_mul_of_nonneg_left hfirstRaw hinv_nonneg
        _ = ‖Ar (x : H) - A x‖ := by
          rw [Real.norm_eq_abs]
          field_simp [habs_ne]
    have hgenerator :
        ‖((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x)‖ =
          ‖Ar (x : H) - A x‖ := by
      rw [← smul_sub, norm_smul]
      simp
    have hthird :
        ‖t‖⁻¹ *
            ‖t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖ =
          ‖Ar (x : H) - A x‖ := by
      rw [norm_smul, hgenerator]
      field_simp [norm_ne_zero_iff.mpr ht0]
    have hdecomp :
        resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H) -
            t • ((-I : ℂ) • A x) =
          (resolventEvolutionStrongLimitOperator A hA t (x : H) -
              resolventApproximationEvolution A hA r hr t (x : H)) +
            (resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
              t • ((-I : ℂ) • Ar (x : H))) +
            t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x)) := by
      module
    have hnorm :
        ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H) -
            t • ((-I : ℂ) • A x)‖ ≤
          ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
              resolventApproximationEvolution A hA r hr t (x : H)‖ +
            ‖resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
              t • ((-I : ℂ) • Ar (x : H))‖ +
            ‖t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖ := by
      rw [hdecomp]
      calc
        ‖(resolventEvolutionStrongLimitOperator A hA t (x : H) -
              resolventApproximationEvolution A hA r hr t (x : H)) +
            (resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
              t • ((-I : ℂ) • Ar (x : H))) +
            t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖ ≤
            ‖(resolventEvolutionStrongLimitOperator A hA t (x : H) -
                resolventApproximationEvolution A hA r hr t (x : H)) +
              (resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
                t • ((-I : ℂ) • Ar (x : H)))‖ +
              ‖t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    have hscaled :
        ‖t‖⁻¹ *
            ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H) -
              t • ((-I : ℂ) • A x)‖ ≤
          ‖t‖⁻¹ *
              ‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
                resolventApproximationEvolution A hA r hr t (x : H)‖ +
            ‖t‖⁻¹ *
              ‖resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
                t • ((-I : ℂ) • Ar (x : H))‖ +
            ‖t‖⁻¹ *
              ‖t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖ := by
      calc
        ‖t‖⁻¹ *
            ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H) -
              t • ((-I : ℂ) • A x)‖ ≤
            ‖t‖⁻¹ *
              (‖resolventEvolutionStrongLimitOperator A hA t (x : H) -
                  resolventApproximationEvolution A hA r hr t (x : H)‖ +
                ‖resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
                  t • ((-I : ℂ) • Ar (x : H))‖ +
                ‖t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖) :=
          mul_le_mul_of_nonneg_left hnorm hinv_nonneg
        _ = _ := by ring
    have htargetNonneg :
        0 ≤ ‖t‖⁻¹ *
          ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H) -
            t • ((-I : ℂ) • A x)‖ :=
      mul_nonneg hinv_nonneg (norm_nonneg _)
    have hmiddle :
        ‖t‖⁻¹ *
            ‖resolventApproximationEvolution A hA r hr t (x : H) - (x : H) -
              t • ((-I : ℂ) • Ar (x : H))‖ < ε / 2 := by
      simpa using ht
    have htarget :
        ‖t‖⁻¹ *
          ‖resolventEvolutionStrongLimitOperator A hA t (x : H) - (x : H) -
            t • ((-I : ℂ) • A x)‖ < ε := by
      have hthird' :
          ‖t‖⁻¹ *
              ‖t • (((-I : ℂ) • Ar (x : H)) - ((-I : ℂ) • A x))‖ < ε / 4 := by
        rw [hthird]
        exact hgen
      exact lt_of_le_of_lt hscaled (by linarith [hfirst, hgen, hmiddle, hthird'])
    simpa [resolventEvolutionStrongLimitOperator_zero, Real.dist_eq,
      abs_of_nonneg htargetNonneg] using htarget

/-- The limiting Stone evolution is differentiable at every time on the original generator domain;
the derivative is the transported generator vector `-i U(t) A x`. -/
theorem resolventEvolutionStrongLimitOperator_apply_hasDerivAt_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    HasDerivAt
      (fun s : ℝ => resolventEvolutionStrongLimitOperator A hA s (x : H))
      ((-I : ℂ) • resolventEvolutionStrongLimitOperator A hA t (A x)) t := by
  let U : ℝ → H →L[ℂ] H := resolventEvolutionStrongLimitOperator A hA
  have hzero := resolventEvolutionStrongLimitOperator_apply_hasDerivAt_zero_domain A hA x
  have hzero' :
      HasDerivAt (fun s : ℝ => U s (x : H)) ((-I : ℂ) • A x) (t + (-t)) := by
    simpa [U] using hzero
  have hshift :
      HasDerivAt (fun s : ℝ => U (s + (-t)) (x : H)) ((-I : ℂ) • A x) t :=
    hzero'.comp_add_const t (-t)
  have hmap :=
    (((U t).restrictScalars ℝ).hasFDerivAt.comp t hshift.hasFDerivAt).hasDerivAt
  have hmap' :
      HasDerivAt
        (fun s : ℝ => U t (U (s + (-t)) (x : H)))
        ((-I : ℂ) • U t (A x)) t := by
    change HasDerivAt
      (fun s : ℝ => U t (U (s + (-t)) (x : H)))
      (U t ((-I : ℂ) • A x)) t at hmap
    rw [(U t).map_smul] at hmap
    exact hmap
  have hfun :
      (fun s : ℝ => U t (U (s + (-t)) (x : H))) =
        (fun s : ℝ => U s (x : H)) := by
    funext s
    have happ := congrArg (fun T : H →L[ℂ] H => T (x : H))
      (resolventEvolutionStrongLimitOperator_add A hA t (s + (-t)))
    have htime : t + (s + (-t)) = s := by ring
    rw [htime] at happ
    simpa [U] using happ.symm
  rw [← hfun]
  simpa [U] using hmap'

/-- Generator form of the Stone differential equation on the invariant domain. -/
theorem resolventEvolutionStrongLimitOperator_apply_hasDerivAt_generator
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    HasDerivAt
      (fun s : ℝ => resolventEvolutionStrongLimitOperator A hA s (x : H))
      ((-I : ℂ) •
        A ⟨resolventEvolutionStrongLimitOperator A hA t (x : H),
          resolventEvolutionStrongLimitOperator_mem_domain A hA t x⟩) t := by
  rw [resolventEvolutionStrongLimitOperator_apply_domain A hA t x]
  exact resolventEvolutionStrongLimitOperator_apply_hasDerivAt_domain A hA t x

end

end LinearPMap