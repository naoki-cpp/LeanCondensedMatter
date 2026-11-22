import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.header false

/-!
# Compact support on real intervals

Pure analytic lemmas relating compactly supported functions to interval integration and
endpoint vanishing. No conservation law or physical dynamics is assumed.
-/

namespace MeasureTheory

noncomputable section

open Set
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

end
end MeasureTheory
