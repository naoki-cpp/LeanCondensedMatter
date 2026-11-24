import LeanCondensedMatter.Analysis.Calculus.CompactSupportInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a b : ℝ)
    {test testDerivative current currentDerivative densityTimeDerivative : ℝ → A}
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b) :
    (∫ x in a..b, test x * densityTimeDerivative x) =
      (∫ x in a..b, testDerivative x * current x) -
        (test b * current b - test a * current a) := by
  have hdensity : densityTimeDerivative = fun x => -currentDerivative x := by
    funext x
    calc
      densityTimeDerivative x =
          densityTimeDerivative x + currentDerivative x - currentDerivative x :=
        (add_sub_cancel_right _ _).symm
      _ = -currentDerivative x := by rw [hcontinuity x, zero_sub]
  rw [hdensity]
  simp only [mul_neg, intervalIntegral.integral_neg,
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      htest hcurrent htestIntegrable hcurrentIntegrable, neg_sub]

/-- A strict support window removes the boundary term and identifies the interval
weak balance with the whole-space identity. -/
theorem weak_continuity_wholeSpace_of_interval
    (a b : ℝ) {test current densityTimeDerivative : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (hInterval :
      (∫ x in a..b, test x * densityTimeDerivative x) =
        (∫ x in a..b, deriv test x * current x) -
          (test b * current b - test a * current a)) :
    (∫ x, test x * densityTimeDerivative x) =
      ∫ x, deriv test x * current x := by
  rcases MeasureTheory.endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  rw [MeasureTheory.integral_mul_eq_integral_of_tsupport_subset_Ioo htestSupport,
    MeasureTheory.integral_deriv_mul_eq_integral_of_tsupport_subset_Ioo htestSupport] at hInterval
  simpa [ha, hb] using hInterval

end
end ConservationLaw
