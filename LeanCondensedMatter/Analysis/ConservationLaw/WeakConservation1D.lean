import LeanCondensedMatter.Analysis.Calculus.CompactSupportInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Abel

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

/-- A pointwise conservation equation implies a weak balance for any continuous bilinear
pairing of test data with currents and density rates. Only the paired derivative terms need
to be interval integrable; no multiplication on the spaces is required. -/
theorem weak_continuity_interval_of_pointwise
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (B : E →L[ℝ] F →L[ℝ] G) (a b : ℝ)
    {test testDerivative : ℝ → E}
    {current currentDerivative densityTimeDerivative : ℝ → F}
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestPair : IntervalIntegrable (fun x => B (testDerivative x) (current x)) volume a b)
    (hcurrentPair : IntervalIntegrable (fun x => B (test x) (currentDerivative x)) volume a b) :
    (∫ x in a..b, B (test x) (densityTimeDerivative x)) =
      (∫ x in a..b, B (testDerivative x) (current x)) -
        (B (test b) (current b) - B (test a) (current a)) := by
  have hdensity : densityTimeDerivative = fun x => -currentDerivative x := by
    funext x
    calc
      densityTimeDerivative x = densityTimeDerivative x + currentDerivative x -
          currentDerivative x := (add_sub_cancel_right _ _).symm
      _ = -currentDerivative x := by rw [hcontinuity x, zero_sub]
  have hsum := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => B.hasDerivAt_of_bilinear (fun _ => htest x hx) (fun _ => hcurrent x hx))
    (hcurrentPair.add htestPair)
  rw [intervalIntegral.integral_add hcurrentPair htestPair] at hsum
  rw [hdensity]
  simp only [map_neg, intervalIntegral.integral_neg]
  rw [← hsum]
  abel

/-- A strict support window removes the boundary term and identifies a weak interval
balance for any continuous bilinear pairing with the corresponding full-line identity. -/
theorem weak_continuity_wholeSpace_of_interval
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a b : ℝ)
    {test : ℝ → E} {current densityTimeDerivative : ℝ → F}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (hInterval :
      (∫ x in a..b, B (test x) (densityTimeDerivative x)) =
        (∫ x in a..b, B (deriv test x) (current x)) -
          (B (test b) (current b) - B (test a) (current a))) :
    (∫ x, B (test x) (densityTimeDerivative x)) =
      ∫ x, B (deriv test x) (current x) := by
  rcases MeasureTheory.endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  have hzero (y : F) : B 0 y = 0 := by simp
  rw [MeasureTheory.integral_pairing_eq_integral_of_tsupport_subset_Ioo
        (fun x y => B x y) hzero htestSupport,
      MeasureTheory.integral_pairing_eq_integral_of_tsupport_subset_Ioo
        (fun x y => B x y) hzero (tsupport_deriv_subset.trans htestSupport)] at hInterval
  simpa [ha, hb, hzero] using hInterval

end
end ConservationLaw
