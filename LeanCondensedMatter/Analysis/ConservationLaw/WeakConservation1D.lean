import LeanCondensedMatter.Analysis.Calculus.CompactSupportInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Generic one-dimensional weak conservation laws

This module derives weak balance identities from pointwise continuity equations.
The physics-independent compact-support integration lemmas live in
`Analysis.Calculus.CompactSupportInterval`.
-/

namespace ConservationLaw

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- A pointwise one-dimensional conservation equation implies the interval weak balance.

The result is

`∫ test * densityRate = ∫ test' * flux - (test(b) * flux(b) - test(a) * flux(a))`.
-/
theorem weak_continuity_interval_of_pointwise
    (a b : ℝ)
    {test testDerivative current currentDerivative densityTimeDerivative : ℝ → ℝ}
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b) :
    (∫ x in a..b, test x * densityTimeDerivative x) =
      (∫ x in a..b, testDerivative x * current x) -
        (test b * current b - test a * current a) := by
  have hpointwiseIntegral :
      (∫ x in a..b, test x * densityTimeDerivative x) =
        -(∫ x in a..b, test x * currentDerivative x) := by
    calc
      (∫ x in a..b, test x * densityTimeDerivative x) =
          ∫ x in a..b, -(test x * currentDerivative x) := by
            apply intervalIntegral.integral_congr_ae
            exact Filter.Eventually.of_forall fun x _ => by
              have hx := hcontinuity x
              have hdensity : densityTimeDerivative x = -currentDerivative x := by
                linarith
              rw [hdensity]
              ring
      _ = -(∫ x in a..b, test x * currentDerivative x) := by
        rw [intervalIntegral.integral_neg]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    htest hcurrent htestIntegrable hcurrentIntegrable
  rw [hpointwiseIntegral, hparts]
  ring

/-- The interval weak balance has no boundary term when the test function vanishes at both
endpoints. -/
theorem weak_continuity_interval_of_pointwise_zero_boundary
    (a b : ℝ)
    {test testDerivative current currentDerivative densityTimeDerivative : ℝ → ℝ}
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b)
    (ha : test a = 0) (hb : test b = 0) :
    (∫ x in a..b, test x * densityTimeDerivative x) =
      ∫ x in a..b, testDerivative x * current x := by
  rw [weak_continuity_interval_of_pointwise a b hcontinuity htest hcurrent
    htestIntegrable hcurrentIntegrable]
  simp [ha, hb]

/-- A pointwise one-dimensional conservation equation gives the whole-space weak identity for a
differentiable test function supported strictly inside a finite interval. -/
theorem weak_continuity_wholeSpace_of_pointwise
    (a b : ℝ)
    {test current currentDerivative densityTimeDerivative : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (htestDifferentiable : Differentiable ℝ test)
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b) :
    (∫ x, test x * densityTimeDerivative x) =
      ∫ x, deriv test x * current x := by
  have htest : ∀ x ∈ [[a, b]], HasDerivAt test (deriv test x) x := by
    intro x _
    exact (htestDifferentiable x).hasDerivAt
  rcases MeasureTheory.endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  have hweak := weak_continuity_interval_of_pointwise_zero_boundary
    a b hcontinuity htest hcurrent htestDerivIntegrable hcurrentIntegrable ha hb
  rw [MeasureTheory.integral_mul_eq_integral_of_tsupport_subset_Ioo htestSupport,
    MeasureTheory.integral_deriv_mul_eq_integral_of_tsupport_subset_Ioo htestSupport] at hweak
  exact hweak

end
end ConservationLaw
