import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventCommutation
import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventConvergence
import LeanCondensedMatter.Analysis.Operator.BoundedUnitaryEvolution
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Strongly continuous Stone evolution

This module constructs the unitary evolution of a self-adjoint LinearPMap and proves its group,
continuity, domain-preservation, and generator laws. Resolvent approximation and strong-limit
arguments are implementation details kept private here.
-/


namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unitary group obtained by exponentiating the bounded resolvent approximation `Aᵣ`. -/
noncomputable def resolventApproximationEvolution
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (t : ℝ) : H →L[ℂ] H :=
  boundedUnitaryEvolution (boundedSelfAdjointApproximation A hA r hr) t

@[simp]
theorem resolventApproximationEvolution_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) :
    resolventApproximationEvolution A hA r hr 0 = 1 := by
  exact boundedUnitaryEvolution_zero _

/-- Each bounded resolvent approximation gives a one-parameter group. -/
theorem resolventApproximationEvolution_add
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (t s : ℝ) :
    resolventApproximationEvolution A hA r hr (t + s) =
      resolventApproximationEvolution A hA r hr t *
        resolventApproximationEvolution A hA r hr s := by
  exact boundedUnitaryEvolution_add _ t s

/-- The resolvent-approximating evolution satisfies its bounded-generator equation vectorwise. -/
theorem resolventApproximationEvolution_apply_hasDerivAt
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (t : ℝ) (x : H) :
    HasDerivAt (fun τ : ℝ => resolventApproximationEvolution A hA r hr τ x)
      ((resolventApproximationEvolution A hA r hr t *
        ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr)) x) t := by
  exact boundedUnitaryEvolution_apply_hasDerivAt _ t x

/-- Difference estimate for the bounded resolvent-approximation evolutions. -/
private theorem norm_resolventApproximationEvolution_sub_le
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
private def boundedSelfAdjointApproximationAtScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) : H →L[ℂ] H :=
  boundedSelfAdjointApproximation A hA (positiveApproximationScale r)
    (positiveApproximationScale_pos r)

/-- A total real-indexed version of the resolvent evolution, obtained by clipping the scale below
at one. -/
private def resolventApproximationEvolutionAtScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) : H →L[ℂ] H :=
  resolventApproximationEvolution A hA (positiveApproximationScale r)
    (positiveApproximationScale_pos r) t

/-- On the original domain, the bounded resolvent evolutions are strongly Cauchy at each fixed
real time. -/
private theorem resolventApproximationEvolution_domain_cauchy
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
private theorem resolventApproximationEvolutionAtScale_apply_domain_cauchySeq
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
  simpa [boundedSelfAdjointApproximationAtScale, positiveApproximationScale,
    max_eq_right h1r, dist_eq_norm] using h

/-- The totalized evolution and generator approximations use the same regularization scale. -/
private theorem norm_resolventApproximationEvolution_sub_atScale_le
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

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A family of isometries that is pointwise Cauchy on a dense set is pointwise Cauchy
everywhere. -/
private theorem cauchySeq_apply_of_isometry_of_dense
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
private theorem resolventApproximationEvolutionAtScale_apply_cauchySeq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    CauchySeq (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x) := by
  apply cauchySeq_apply_of_isometry_of_dense
    (fun r y => resolventApproximationEvolutionAtScale A hA r t y)
    hA.dense_domain
  · intro r
    rw [isometry_iff_dist_eq]
    intro y z
    unfold resolventApproximationEvolutionAtScale resolventApproximationEvolution
    rw [dist_eq_norm, dist_eq_norm, ←
      (boundedUnitaryEvolution (boundedSelfAdjointApproximation A hA _ _) t).map_sub]
    apply boundedUnitaryEvolution_apply_norm
    exact boundedSelfAdjointApproximation_isSelfAdjoint A hA _ _
  · intro y hy
    exact resolventApproximationEvolutionAtScale_apply_domain_cauchySeq
      A hA t ⟨y, hy⟩

/-- The vectorwise strong limit of the resolvent-approximating unitary evolutions. -/
private def resolventEvolutionStrongLimit
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) : H :=
  limUnder atTop (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x)

/-- The totalized resolvent approximations converge strongly to `resolventEvolutionStrongLimit`. -/
private theorem tendsto_resolventApproximationEvolutionAtScale_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    Tendsto (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x)
      atTop (𝓝 (resolventEvolutionStrongLimit A hA t x)) := by
  simpa [resolventEvolutionStrongLimit] using
    (resolventApproximationEvolutionAtScale_apply_cauchySeq A hA t x).tendsto_limUnder

end

end LinearPMap

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized bounded approximating evolution preserves vector norms. -/
private theorem resolventApproximationEvolutionAtScale_apply_norm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) (x : H) :
    ‖resolventApproximationEvolutionAtScale A hA r t x‖ = ‖x‖ := by
  unfold resolventApproximationEvolutionAtScale resolventApproximationEvolution
  apply boundedUnitaryEvolution_apply_norm
  exact boundedSelfAdjointApproximation_isSelfAdjoint A hA _ _

/-- The strong-limit Stone evolution preserves vector norms. -/
private theorem resolventEvolutionStrongLimit_apply_norm
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

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized bounded approximants retain the zero-time identity. -/
@[simp]
private theorem resolventApproximationEvolutionAtScale_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) :
    resolventApproximationEvolutionAtScale A hA r 0 = 1 := by
  unfold resolventApproximationEvolutionAtScale
  exact resolventApproximationEvolution_zero A hA _ _

/-- The totalized bounded approximants preserve distances. -/
private theorem resolventApproximationEvolutionAtScale_dist_eq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) (x y : H) :
    dist (resolventApproximationEvolutionAtScale A hA r t x)
        (resolventApproximationEvolutionAtScale A hA r t y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm,
    ← (resolventApproximationEvolutionAtScale A hA r t).map_sub]
  exact resolventApproximationEvolutionAtScale_apply_norm A hA r t (x - y)

/-- The strong-limit evolution is the identity at time zero, pointwise. -/
private theorem resolventEvolutionStrongLimit_zero_apply
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
private theorem resolventEvolutionStrongLimit_add_time_apply
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

/-- Star/adjoint reverses time for the limiting evolution. -/
theorem stoneEvolution_star
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (stoneEvolution A hA t) =
      stoneEvolution A hA (-t) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hinner :=
    (LinearMap.norm_map_iff_inner_map_map (stoneEvolution A hA t)).mp
      (fun z => by
        simpa using resolventEvolutionStrongLimit_apply_norm A hA t z)
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
  rw [stoneEvolution_star, ← stoneEvolution_add]
  simp

/-- The limiting evolution is unitary, right-inverse form. -/
theorem stoneEvolution_mul_star
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneEvolution A hA t *
        star (stoneEvolution A hA t) = 1 := by
  rw [stoneEvolution_star, ← stoneEvolution_add]
  simp

end

end LinearPMap

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On the original generator domain, every totalized bounded approximant has displacement bounded
uniformly in the approximation scale by the original generator. -/
private theorem norm_resolventApproximationEvolutionAtScale_apply_sub_le_domain
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
theorem norm_stoneEvolution_apply_sub_le_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    ‖stoneEvolution A hA t (x : H) - (x : H)‖ ≤
      ‖A x‖ * |t| := by
  have hconv :
      Tendsto
        (fun r : ℝ =>
          ‖resolventApproximationEvolutionAtScale A hA r t (x : H) - (x : H)‖)
        atTop
        (𝓝 ‖stoneEvolution A hA t (x : H) - (x : H)‖) := by
    simpa using
      ((tendsto_resolventApproximationEvolutionAtScale_apply A hA t (x : H)).sub_const
        (x : H)).norm
  exact le_of_tendsto hconv <|
    Filter.Eventually.of_forall fun r =>
      norm_resolventApproximationEvolutionAtScale_apply_sub_le_domain A hA r t x

/-- For a vector in the generator domain, the limiting evolution is continuous at time zero. -/
theorem stoneEvolution_apply_continuousAt_zero_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    ContinuousAt (fun t : ℝ => stoneEvolution A hA t (x : H)) 0 := by
  apply continuousAt_of_locally_lipschitz zero_lt_one ‖A x‖
  intro t _
  simpa [stoneEvolution_zero, dist_eq_norm, Real.dist_eq] using
    norm_stoneEvolution_apply_sub_le_domain A hA t x

/-- On the generator domain, the limiting Stone evolution is continuous at every time. -/
theorem stoneEvolution_apply_continuous_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    Continuous (fun t : ℝ => stoneEvolution A hA t (x : H)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hshift :
      ContinuousAt (fun t : ℝ => stoneEvolution A hA (t - s) (x : H)) s := by
    simpa [Function.comp_def] using
      (stoneEvolution_apply_continuousAt_zero_domain A hA x).comp_of_eq
        (by fun_prop) (by simp)
  have hmapped :
      ContinuousAt
        (fun t : ℝ =>
          stoneEvolution A hA s
            (stoneEvolution A hA (t - s) (x : H))) s := by
    simpa [Function.comp_def] using
      (stoneEvolution A hA s).continuous.continuousAt.comp hshift
  convert hmapped using 1
  funext t
  simpa only [stoneEvolution_apply, show s + (t - s) = t by ring] using
    resolventEvolutionStrongLimit_add_time_apply A hA s (t - s) (x : H)

/-- The limiting Stone evolution is jointly continuous in the vector and time variables.
Continuity on the dense generator domain extends to the whole Hilbert space because every time
slice is an isometry. -/
theorem stoneEvolution_joint_continuous
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    Continuous (fun p : H × ℝ => stoneEvolution A hA p.2 p.1) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hA.dense_domain
  · intro x hx
    exact stoneEvolution_apply_continuous_domain A hA ⟨x, hx⟩
  · intro t
    exact (isometry_iff_dist_eq.mpr fun x y => stoneEvolution_dist_eq A hA t x y).lipschitzWith

/-- The limiting unitary group is strongly continuous: every orbit `t ↦ U(t)x` is continuous. -/
theorem stoneEvolution_apply_continuous
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    Continuous (fun t : ℝ => stoneEvolution A hA t x) := by
  have hpair : Continuous (fun t : ℝ => (x, t)) :=
    continuous_const.prodMk continuous_id
  have hcomp :=
    (stoneEvolution_joint_continuous A hA).comp hpair
  have horbit :
      ((fun p : H × ℝ => stoneEvolution A hA p.2 p.1) ∘ fun t : ℝ => (x, t)) =
        fun t : ℝ => stoneEvolution A hA t x := rfl
  rw [horbit] at hcomp
  exact hcomp

end

end LinearPMap

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded self-adjoint approximant commutes with every nonreal resolvent. -/
private theorem boundedSelfAdjointApproximation_nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z.im ≠ 0) :
    Commute (boundedSelfAdjointApproximation A hA r hr)
      (nonrealResolvent A hA z hz) := by
  unfold boundedSelfAdjointApproximation
  apply Commute.smul_left
  apply Commute.add_left
  · exact nonrealResolvent_commute A hA ((r : ℂ) * I) z
      (by simpa using ne_of_gt hr) hz
  · exact nonrealResolvent_commute A hA (star ((r : ℂ) * I)) z
      (by simpa using neg_ne_zero.mpr (ne_of_gt hr)) hz

/-- Nonreal resolvent commutation passes through the vectorwise strong limit. -/
private theorem stoneEvolution_nonrealResolvent_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    stoneEvolution A hA t (nonrealResolvent A hA z hz y) =
      nonrealResolvent A hA z hz (stoneEvolution A hA t y) := by
  have hleft :=
    tendsto_resolventApproximationEvolutionAtScale_apply A hA t
      (nonrealResolvent A hA z hz y)
  have hright :
      Tendsto
        (fun r : ℝ =>
          nonrealResolvent A hA z hz
            (resolventApproximationEvolutionAtScale A hA r t y))
        atTop
        (𝓝 (nonrealResolvent A hA z hz
          (stoneEvolution A hA t y))) := by
    exact ((nonrealResolvent A hA z hz).continuous.tendsto _).comp
      (tendsto_resolventApproximationEvolutionAtScale_apply A hA t y)
  exact tendsto_nhds_unique
    (hleft.congr' (Eventually.of_forall fun r => by
      have hcomm :
          Commute (resolventApproximationEvolutionAtScale A hA r t)
            (nonrealResolvent A hA z hz) := by
        unfold resolventApproximationEvolutionAtScale
          resolventApproximationEvolution boundedUnitaryEvolution
        exact
          ((boundedSelfAdjointApproximation_nonrealResolvent_commute A hA _ _ z hz).smul_left _).exp_left
      have happ := congrArg (fun T : H →L[ℂ] H => T y) hcomm.eq
      simpa using happ))
    hright

/-- The limiting Stone evolution preserves the original self-adjoint operator domain. -/
theorem stoneEvolution_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    stoneEvolution A hA t (x : H) ∈ A.domain := by
  let z : ℂ := I
  have hz : z.im ≠ 0 := by
    norm_num [z]
  let y : H := A x - z • (x : H)
  have hxrepr : nonrealResolvent A hA z hz y = (x : H) := by
    dsimp [y]
    rw [(nonrealResolvent A hA z hz).map_sub,
      (nonrealResolvent A hA z hz).map_smul,
      nonrealResolvent_apply_operator A hA z hz x]
    module
  have hcomm :=
    stoneEvolution_nonrealResolvent_apply A hA t z hz y
  have hrepr :
      stoneEvolution A hA t (x : H) =
        nonrealResolvent A hA z hz
          (stoneEvolution A hA t y) := by
    calc
      stoneEvolution A hA t (x : H) =
          stoneEvolution A hA t
            (nonrealResolvent A hA z hz y) := by rw [hxrepr]
      _ = nonrealResolvent A hA z hz
            (stoneEvolution A hA t y) := hcomm
  rw [hrepr]
  exact nonrealResolvent_mem_domain A hA z hz _

/-- On its original domain, the unbounded self-adjoint generator intertwines with the limiting
Stone evolution. -/
theorem stoneEvolution_apply_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    A ⟨stoneEvolution A hA t (x : H),
        stoneEvolution_mem_domain A hA t x⟩ =
      stoneEvolution A hA t (A x) := by
  let U : H →L[ℂ] H := stoneEvolution A hA t
  let z : ℂ := I
  have hz : z.im ≠ 0 := by
    simpa [z] using I_im_ne_zero
  let R : H →L[ℂ] H := nonrealResolvent A hA z hz
  let y : H := A x - z • (x : H)
  have hxrepr : R y = (x : H) := by
    dsimp [R, y]
    rw [(nonrealResolvent A hA z hz).map_sub,
      (nonrealResolvent A hA z hz).map_smul,
      nonrealResolvent_apply_operator A hA z hz x]
    module
  have hcomm : U (R y) = R (U y) := by
    exact stoneEvolution_nonrealResolvent_apply A hA t z hz y
  have hUrepr : U (x : H) = R (U y) := by
    calc
      U (x : H) = U (R y) := by rw [hxrepr]
      _ = R (U y) := hcomm
  let ux : A.domain :=
    ⟨U (x : H), stoneEvolution_mem_domain A hA t x⟩
  let rx : A.domain :=
    ⟨R (U y), nonrealResolvent_mem_domain A hA z hz (U y)⟩
  have huxrx : ux = rx := by
    apply Subtype.ext
    exact hUrepr
  change A ux = U (A x)
  rw [huxrx]
  have hshift : A rx - z • R (U y) = U y := by
    simpa [rx, R] using apply_nonrealResolvent_sub_smul A hA z hz (U y)
  have hAeq : A rx = U y + z • R (U y) :=
    (sub_eq_iff_eq_add).mp hshift
  have hUy : U y = U (A x) - z • U (x : H) := by
    dsimp [y]
    rw [U.map_sub, U.map_smul]
  calc
    A rx = U y + z • R (U y) := hAeq
    _ = (U (A x) - z • U (x : H)) + z • U (x : H) := by
      rw [← hUrepr, hUy]
    _ = U (A x) := by module

end

end LinearPMap

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A fixed bounded approximating evolution differs from the limiting evolution by at most its
generator error times `|t|`, on the original generator domain. -/
private theorem norm_stoneEvolution_sub_resolventApproximationEvolution_le
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
      have hpair := norm_resolventApproximationEvolution_sub_atScale_le
        A hA r hr s t (x : H)
      linarith
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
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul]
  change |t⁻¹| *
      ‖stoneEvolution A hA t (x : H) -
        resolventApproximationEvolution A hA r hr t (x : H)‖ ≤ _
  rw [abs_inv]
  calc
    |t|⁻¹ *
        ‖stoneEvolution A hA t (x : H) -
          resolventApproximationEvolution A hA r hr t (x : H)‖
        ≤ |t|⁻¹ *
            (‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ * |t|) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (abs_nonneg t))
    _ = ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ := by
      rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]

/-- At zero time, the strong Stone evolution has infinitesimal generator `-i A` on `A.domain`. -/
theorem stoneEvolution_apply_hasDerivAt_zero
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) :
    HasDerivAt (fun t : ℝ => stoneEvolution A hA t (x : H))
      ((-I : ℂ) • A x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add]
  simp only [stoneEvolution_zero, one_apply_eq_self]
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
    have h :=
      resolventApproximationEvolution_apply_hasDerivAt A hA r hr 0 (x : H)
    rw [resolventApproximationEvolution_zero, one_mul] at h
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
    simpa [resolventApproximationEvolution_zero] using htapp
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
  have hzero := stoneEvolution_apply_hasDerivAt_zero A hA x
  have hmapped :=
    ((stoneEvolution A hA s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hzero
  have htranslated :
      HasDerivAt
        (fun h : ℝ => stoneEvolution A hA (s + h) (x : H))
        ((-I : ℂ) • stoneEvolution A hA s (A x)) 0 := by
    convert hmapped using 1
    · funext h
      rw [stoneEvolution_add]
      rfl
    · change
        (-I : ℂ) • stoneEvolution A hA s (A x) =
          stoneEvolution A hA s ((-I : ℂ) • A x)
      symm
      exact (stoneEvolution A hA s).map_smul _ _
  have hshift :=
    htranslated.scomp_of_eq s ((hasDerivAt_id s).sub_const s) (by simp)
  have hshift' := hshift
  simp only [id_eq, one_smul] at hshift'
  convert hshift' using 1
  funext t
  simp [Function.comp_apply]

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
