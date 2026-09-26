import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventCommutation
import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedUnitaryEvolution
import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedUnitaryEvolutionEstimate
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Strong Cauchy estimates for the bounded Stone evolutions

The bounded self-adjoint approximants `Aᵣ` commute at different positive regularization scales.
Therefore their exponential evolutions factor through the difference generator `Aᵣ - Aₛ`.
Combining this with the bounded displacement estimate gives

`‖Uᵣ(t)x - Uₛ(t)x‖ ≤ ‖(Aᵣ - Aₛ)x‖ |t|`.

On the domain of the original self-adjoint operator, the strong convergence `Aᵣ x → A x` then
makes the approximating unitary evolutions a Cauchy family for every fixed time.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference estimate for the bounded resolvent-approximation evolutions. -/
theorem norm_resolventApproximationEvolution_sub_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (t : ℝ) (x : H) :
    ‖resolventApproximationEvolution A hA r hr t x -
        resolventApproximationEvolution A hA s hs t x‖ ≤
      ‖(boundedSelfAdjointApproximation A hA r hr -
          boundedSelfAdjointApproximation A hA s hs) x‖ * |t| := by
  let Ar : H →L[ℂ] H := boundedSelfAdjointApproximation A hA r hr
  let As : H →L[ℂ] H := boundedSelfAdjointApproximation A hA s hs
  let D : H →L[ℂ] H := Ar - As
  have hAr : IsSelfAdjoint Ar := by
    exact boundedSelfAdjointApproximation_isSelfAdjoint A hA r hr
  have hAs : IsSelfAdjoint As := by
    exact boundedSelfAdjointApproximation_isSelfAdjoint A hA s hs
  have hArAs : Commute Ar As := by
    exact boundedSelfAdjointApproximation_commute A hA r s hr hs
  have hAsD : Commute As D := by
    exact hArAs.symm.sub_right (Commute.refl As)
  have hD : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff]
    have hArstar : star Ar = Ar := by
      simpa only [isSelfAdjoint_iff] using hAr
    have hAsstar : star As = As := by
      simpa only [isSelfAdjoint_iff] using hAs
    simp [D, star_sub, hArstar, hAsstar]
  have hadd : As + D = Ar := by
    simp [D]
  have hfactor :
      boundedUnitaryEvolution Ar t =
        boundedUnitaryEvolution As t * boundedUnitaryEvolution D t := by
    rw [← hadd]
    exact boundedUnitaryEvolution_add_generator_of_commute As D hAsD t
  change ‖boundedUnitaryEvolution Ar t x - boundedUnitaryEvolution As t x‖ ≤ ‖D x‖ * |t|
  rw [hfactor]
  change
    ‖boundedUnitaryEvolution As t (boundedUnitaryEvolution D t x) -
        boundedUnitaryEvolution As t x‖ ≤ ‖D x‖ * |t|
  rw [← (boundedUnitaryEvolution As t).map_sub]
  rw [boundedUnitaryEvolution_apply_norm As hAs t]
  exact norm_boundedUnitaryEvolution_apply_sub_le D hD t x

private def positiveApproximationScale (r : ℝ) : ℝ :=
  max 1 r

private theorem positiveApproximationScale_pos (r : ℝ) :
    0 < positiveApproximationScale r := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 r)

/-- A total real-indexed version of the bounded resolvent approximation. -/
noncomputable def boundedSelfAdjointApproximationAtScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) : H →L[ℂ] H :=
  boundedSelfAdjointApproximation A hA (positiveApproximationScale r)
    (positiveApproximationScale_pos r)

/-- A total real-indexed version of the resolvent evolution, obtained by clipping the scale below
at one. -/
noncomputable def resolventApproximationEvolutionAtScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) : H →L[ℂ] H :=
  resolventApproximationEvolution A hA (positiveApproximationScale r)
    (positiveApproximationScale_pos r) t

/-- On the original domain, the bounded resolvent evolutions are strongly Cauchy at each fixed
real time. -/
theorem resolventApproximationEvolution_domain_cauchy
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain)
    (t : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ r s : ℝ, R ≤ r → R ≤ s →
      ∀ hr : 0 < r, ∀ hs : 0 < s,
        ‖resolventApproximationEvolution A hA r hr t (x : H) -
            resolventApproximationEvolution A hA s hs t (x : H)‖ < ε := by
  by_cases ht : t = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro r s _ _ hr hs
    simpa [ht, resolventApproximationEvolution_zero] using hε
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hden : 0 < 2 * |t| := by positivity
    have hδ : 0 < ε / (2 * |t|) := by positivity
    obtain ⟨R, hR, hconv⟩ :=
      boundedSelfAdjointApproximation_strong_convergence A hA x
        (ε / (2 * |t|)) hδ
    refine ⟨R, hR, ?_⟩
    intro r s hRr hRs hr hs
    have hrconv := hconv r hRr hr
    have hsconv := hconv s hRs hs
    have hrscaled :
        ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * (2 * |t|) < ε :=
      (lt_div_iff₀ hden).mp hrconv
    have hsscaled :
        ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ * (2 * |t|) < ε :=
      (lt_div_iff₀ hden).mp hsconv
    have hrhalf :
        ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t| < ε / 2 := by
      have h := hrscaled
      have hre :
          ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * (2 * |t|) =
            2 * (‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t|) := by
        ring
      rw [hre] at h
      linarith
    have hshalf :
        ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ * |t| < ε / 2 := by
      have h := hsscaled
      have hre :
          ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ * (2 * |t|) =
            2 * (‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ * |t|) := by
        ring
      rw [hre] at h
      linarith
    have hdiff :
        ‖(boundedSelfAdjointApproximation A hA r hr -
            boundedSelfAdjointApproximation A hA s hs) (x : H)‖ ≤
          ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ +
            ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ := by
      calc
        ‖(boundedSelfAdjointApproximation A hA r hr -
            boundedSelfAdjointApproximation A hA s hs) (x : H)‖ =
            ‖(boundedSelfAdjointApproximation A hA r hr (x : H) - A x) -
              (boundedSelfAdjointApproximation A hA s hs (x : H) - A x)‖ := by
                congr 1
                change
                  boundedSelfAdjointApproximation A hA r hr (x : H) -
                      boundedSelfAdjointApproximation A hA s hs (x : H) =
                    (boundedSelfAdjointApproximation A hA r hr (x : H) - A x) -
                      (boundedSelfAdjointApproximation A hA s hs (x : H) - A x)
                abel
        _ ≤ ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ +
              ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ :=
            norm_sub_le _ _
    have hsum :
        (‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ +
          ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖) * |t| < ε := by
      calc
        (‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ +
            ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖) * |t| =
            ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t| +
              ‖boundedSelfAdjointApproximation A hA s hs (x : H) - A x‖ * |t| := by
                rw [add_mul]
        _ < ε := by linarith
    have hmul :
        ‖(boundedSelfAdjointApproximation A hA r hr -
            boundedSelfAdjointApproximation A hA s hs) (x : H)‖ * |t| < ε := by
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdiff (abs_nonneg t)) hsum
    exact lt_of_le_of_lt
      (norm_resolventApproximationEvolution_sub_le A hA r s hr hs t (x : H)) hmul

/-- On the generator domain, the totalized resolvent evolutions form a Cauchy sequence at
positive infinity. -/
theorem resolventApproximationEvolutionAtScale_apply_domain_cauchySeq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    CauchySeq (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t (x : H)) := by
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  obtain ⟨R, hR, hcauchy⟩ :=
    resolventApproximationEvolution_domain_cauchy A hA x t ε hε
  refine ⟨max R 1, ?_⟩
  intro r hr s hs
  have hRr : R ≤ r := (le_max_left R 1).trans hr
  have hRs : R ≤ s := (le_max_left R 1).trans hs
  have h1r : 1 ≤ r := (le_max_right R 1).trans hr
  have h1s : 1 ≤ s := (le_max_right R 1).trans hs
  have hrpos : 0 < r := zero_lt_one.trans_le h1r
  have hspos : 0 < s := zero_lt_one.trans_le h1s
  have hnorm := hcauchy r s hRr hRs hrpos hspos
  simpa [dist_eq_norm, resolventApproximationEvolutionAtScale, positiveApproximationScale,
    max_eq_right h1r, max_eq_right h1s] using hnorm

/-- On the original domain, the totalized bounded approximations converge strongly to the
self-adjoint operator. -/
theorem boundedSelfAdjointApproximationAtScale_apply_tendsto
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
  simpa [boundedSelfAdjointApproximationAtScale, positiveApproximationScale,
    max_eq_right h1r, dist_eq_norm] using h

/-- The totalized evolution and generator approximations use the same regularization scale. -/
theorem norm_resolventApproximationEvolution_sub_atScale_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (s t : ℝ) (x : H) :
    ‖resolventApproximationEvolution A hA r hr t x -
        resolventApproximationEvolutionAtScale A hA s t x‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr x -
          boundedSelfAdjointApproximationAtScale A hA s x‖ * |t| := by
  change
    ‖resolventApproximationEvolution A hA r hr t x -
        resolventApproximationEvolution A hA (positiveApproximationScale s)
          (positiveApproximationScale_pos s) t x‖ ≤
      ‖boundedSelfAdjointApproximation A hA r hr x -
          boundedSelfAdjointApproximation A hA (positiveApproximationScale s)
            (positiveApproximationScale_pos s) x‖ * |t|
  exact norm_resolventApproximationEvolution_sub_le
    A hA r (positiveApproximationScale s) hr (positiveApproximationScale_pos s) t x


end

end LinearPMap
