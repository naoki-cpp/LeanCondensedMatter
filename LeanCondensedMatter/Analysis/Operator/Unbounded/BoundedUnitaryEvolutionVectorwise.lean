import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedUnitaryEvolution
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option linter.style.header false

/-!
# Vectorwise bounded unitary evolution

This file exposes the strong-continuity and vectorwise derivative statements for the bounded
unitary groups used in the resolvent approximation to Stone's theorem.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Operator-norm continuity of the bounded evolution implies strong continuity on every vector. -/
theorem boundedUnitaryEvolution_apply_continuous (B : H →L[ℂ] H) (x : H) :
    Continuous (fun t : ℝ => boundedUnitaryEvolution B t x) := by
  exact ((ContinuousLinearMap.apply ℂ H) x).continuous.comp
    (boundedUnitaryEvolution_continuous B)

/-- The bounded-generator differential equation after evaluating the propagator on a vector. -/
theorem boundedUnitaryEvolution_apply_hasDerivAt (B : H →L[ℂ] H) (t : ℝ) (x : H) :
    HasDerivAt (fun τ : ℝ => boundedUnitaryEvolution B τ x)
      ((boundedUnitaryEvolution B t * ((-I : ℂ) • B)) x) t := by
  have h := (((ContinuousLinearMap.apply ℂ H) x).restrictScalars ℝ).hasFDerivAt.comp t
    (boundedUnitaryEvolution_hasDerivAt B t).hasFDerivAt
  simpa [Function.comp_def] using h.hasDerivAt

/-- The resolvent-approximating evolution satisfies its bounded-generator equation vectorwise. -/
theorem resolventApproximationEvolution_apply_hasDerivAt
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (t : ℝ) (x : H) :
    HasDerivAt (fun τ : ℝ => resolventApproximationEvolution A hA r hr τ x)
      ((resolventApproximationEvolution A hA r hr t *
        ((-I : ℂ) • boundedSelfAdjointApproximation A hA r hr)) x) t := by
  exact boundedUnitaryEvolution_apply_hasDerivAt _ t x

end

end LinearPMap
