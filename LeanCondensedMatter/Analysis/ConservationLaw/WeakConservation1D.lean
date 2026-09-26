import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Generic one-dimensional weak conservation laws

This module contains the one-dimensional integration-by-parts kernel shared by continuum
conservation laws.  It does not mention probability, Schrödinger dynamics, or any particular
physical current.
-/

namespace ConservationLaw

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- A function supported strictly inside an interval makes its product with any function
interval-integrable and whole-space integrable through the interval support theorem. -/
theorem integral_mul_eq_integral_of_tsupport_subset_Ioo
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    (∫ x in a..b, f x * g x) = ∫ x, f x * g x := by
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (by
      intro x hx
      have hfx : f x ≠ 0 := by
        intro hzero
        apply hx
        simp [hzero]
      have hxTop : x ∈ tsupport f := subset_closure hfx
      have hxab := hf hxTop
      exact ⟨hxab.1, hxab.2.le⟩)

/-- The derivative of a function supported strictly inside an interval has the same support
window for the purpose of multiplying by an arbitrary function. -/
theorem integral_deriv_mul_eq_integral_of_tsupport_subset_Ioo
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    (∫ x in a..b, deriv f x * g x) = ∫ x, deriv f x * g x := by
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (by
      intro x hx
      have hdx : deriv f x ≠ 0 := by
        intro hzero
        apply hx
        simp [hzero]
      have hxTop : x ∈ tsupport f := support_deriv_subset hdx
      have hxab := hf hxTop
      exact ⟨hxab.1, hxab.2.le⟩)

/-- A function whose topological support is strictly inside an interval vanishes at both
endpoints. -/
theorem endpoint_values_eq_zero_of_tsupport_subset_Ioo
    {a b : ℝ} {f : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    f a = 0 ∧ f b = 0 := by
  constructor
  · by_contra ha
    have haTop : a ∈ tsupport f := subset_closure ha
    exact (lt_irrefl a (hf haTop).1)
  · by_contra hb
    have hbTop : b ∈ tsupport f := subset_closure hb
    exact (lt_irrefl b (hf hbTop).2)

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
  rcases endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  have hweak := weak_continuity_interval_of_pointwise_zero_boundary
    a b hcontinuity htest hcurrent htestDerivIntegrable hcurrentIntegrable ha hb
  rw [integral_mul_eq_integral_of_tsupport_subset_Ioo htestSupport,
    integral_deriv_mul_eq_integral_of_tsupport_subset_Ioo htestSupport] at hweak
  exact hweak

end
end ConservationLaw
