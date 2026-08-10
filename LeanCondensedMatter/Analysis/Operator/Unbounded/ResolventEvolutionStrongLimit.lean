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
open scoped InnerProductSpace

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

/-- The resolvent-approximating evolutions are strongly Cauchy on every vector, not only on the
original generator domain. -/
theorem resolventApproximationEvolution_cauchy
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (t : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ r s : ℝ, R ≤ r → R ≤ s →
      ∀ hr : 0 < r, ∀ hs : 0 < s,
        ‖resolventApproximationEvolution A hA r hr t x -
            resolventApproximationEvolution A hA s hs t x‖ < ε := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨y, hyA, hxy⟩ := hA.dense_domain.exists_dist_lt x hε4
  let yA : A.domain := ⟨y, hyA⟩
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨R, hR, hdom⟩ :=
    resolventApproximationEvolution_domain_cauchy A hA yA t (ε / 2) hε2
  refine ⟨R, hR, ?_⟩
  intro r s hRr hRs hr hs
  have hleft :
      dist (resolventApproximationEvolution A hA r hr t x)
          (resolventApproximationEvolution A hA r hr t y) < ε / 4 := by
    rw [resolventApproximationEvolution_dist_eq A hA r hr t x y]
    exact hxy
  have hmid :
      dist (resolventApproximationEvolution A hA r hr t y)
          (resolventApproximationEvolution A hA s hs t y) < ε / 2 := by
    simpa [dist_eq_norm, yA] using hdom r s hRr hRs hr hs
  have hyx : dist y x < ε / 4 := by
    rw [dist_comm]
    exact hxy
  have hright :
      dist (resolventApproximationEvolution A hA s hs t y)
          (resolventApproximationEvolution A hA s hs t x) < ε / 4 := by
    rw [resolventApproximationEvolution_dist_eq A hA s hs t y x]
    exact hyx
  have hdist :
      dist (resolventApproximationEvolution A hA r hr t x)
          (resolventApproximationEvolution A hA s hs t x) < ε := by
    have htri :
        dist (resolventApproximationEvolution A hA r hr t x)
            (resolventApproximationEvolution A hA s hs t x) ≤
          dist (resolventApproximationEvolution A hA r hr t x)
              (resolventApproximationEvolution A hA r hr t y) +
            (dist (resolventApproximationEvolution A hA r hr t y)
                (resolventApproximationEvolution A hA s hs t y) +
              dist (resolventApproximationEvolution A hA s hs t y)
                (resolventApproximationEvolution A hA s hs t x)) := by
      calc
        dist (resolventApproximationEvolution A hA r hr t x)
            (resolventApproximationEvolution A hA s hs t x) ≤
            dist (resolventApproximationEvolution A hA r hr t x)
                (resolventApproximationEvolution A hA r hr t y) +
              dist (resolventApproximationEvolution A hA r hr t y)
                (resolventApproximationEvolution A hA s hs t x) :=
          dist_triangle _ _ _
        _ ≤ dist (resolventApproximationEvolution A hA r hr t x)
                (resolventApproximationEvolution A hA r hr t y) +
              (dist (resolventApproximationEvolution A hA r hr t y)
                  (resolventApproximationEvolution A hA s hs t y) +
                dist (resolventApproximationEvolution A hA s hs t y)
                  (resolventApproximationEvolution A hA s hs t x)) := by
          exact add_le_add_left (dist_triangle _ _ _) _
    exact lt_of_le_of_lt htri (by linarith)
  simpa [dist_eq_norm] using hdist

private def positiveApproximationScale (r : ℝ) : ℝ :=
  max 1 r

private theorem positiveApproximationScale_pos (r : ℝ) :
    0 < positiveApproximationScale r := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 r)

/-- A total `ℝ`-indexed version of the resolvent evolution, obtained by clipping the scale below
at `1`.  This agrees with the original positive-scale evolution eventually at `+∞`. -/
noncomputable def resolventApproximationEvolutionAtScale
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r t : ℝ) : H →L[ℂ] H :=
  resolventApproximationEvolution A hA (positiveApproximationScale r)
    (positiveApproximationScale_pos r) t

/-- For every fixed time and vector, the totalized resolvent approximations are a Cauchy sequence
as the real scale tends to `+∞`. -/
theorem resolventApproximationEvolutionAtScale_apply_cauchySeq
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    CauchySeq (fun r : ℝ => resolventApproximationEvolutionAtScale A hA r t x) := by
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  obtain ⟨R, hR, hcauchy⟩ := resolventApproximationEvolution_cauchy A hA x t ε hε
  refine ⟨max R 1, ?_⟩
  intro r hr s hs
  have hRr : R ≤ r := (le_max_left R 1).trans hr
  have hRs : R ≤ s := (le_max_left R 1).trans hs
  have h1r : 1 ≤ r := (le_max_right R 1).trans hr
  have h1s : 1 ≤ s := (le_max_right R 1).trans hs
  have hrpos : 0 < r := zero_lt_one.trans_le h1r
  have hspos : 0 < s := zero_lt_one.trans_le h1s
  have hnorm := hcauchy r s hRr hRs hrpos hspos
  have hdist :
      dist (resolventApproximationEvolution A hA r hrpos t x)
          (resolventApproximationEvolution A hA s hspos t x) < ε := by
    simpa [dist_eq_norm] using hnorm
  simpa [resolventApproximationEvolutionAtScale, positiveApproximationScale,
    max_eq_right h1r, max_eq_right h1s] using hdist

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
