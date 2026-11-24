import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Real interval-to-full-line integration

Pure analytic lemmas relating compactly supported functions to interval integration and
endpoint vanishing, together with a full-line encoding of an oriented interval integral using
indicator functions. No conservation law, transport convention, or physical dynamics is assumed.
-/

namespace MeasureTheory

noncomputable section

open Set
open scoped Interval

/-- A product supported inside the interval has the same interval and full-line integrals.
No integrability assertion is needed for this equality of total integrals. -/
theorem integral_mul_eq_integral_of_tsupport_subset_Ioo
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    (∫ x in a..b, f x * g x) = ∫ x, f x * g x := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  exact (Function.support_mul_subset_left f g).trans
    (subset_closure.trans (hf.trans fun _ hx => ⟨hx.1, hx.2.le⟩))

/-- The derivative has topological support contained in that of the original function. -/
theorem integral_deriv_mul_eq_integral_of_tsupport_subset_Ioo
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    (∫ x in a..b, deriv f x * g x) = ∫ x, deriv f x * g x :=
  integral_mul_eq_integral_of_tsupport_subset_Ioo (tsupport_deriv_subset.trans hf)

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

/-!
# Full-line localization of oriented interval integrals

Mathlib's `intervalIntegral` already carries the orientation of an integral from `a` to `b`. This
module supplies the complementary full-line realization used by downstream energy-kernel
constructions: the integrand on `(a, b]` minus the integrand on `(b, a]`.

The construction is representation-independent and contains no transport assumptions.
-/

namespace MeasureTheory

open Set

noncomputable section

/-- A full-line function encoding the oriented interval integral from `a` to `b`. -/
noncomputable def orientedIntervalIntegrand {E : Type*} [AddGroup E]
    (f : ℝ → E) (a b energy : ℝ) : E :=
  (Ioc a b).indicator f energy - (Ioc b a).indicator f energy

theorem integrable_orientedIntervalIntegrand {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    Integrable (orientedIntervalIntegrand f a b) := by
  unfold orientedIntervalIntegrand
  exact (hf.1.integrable_indicator measurableSet_Ioc).sub
    (hf.2.integrable_indicator measurableSet_Ioc)

theorem integral_orientedIntervalIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    (∫ energy : ℝ, orientedIntervalIntegrand f a b energy) =
      ∫ energy in a..b, f energy := by
  unfold orientedIntervalIntegrand
  rw [MeasureTheory.integral_sub
    (hf.1.integrable_indicator measurableSet_Ioc)
    (hf.2.integrable_indicator measurableSet_Ioc)]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc]
  rfl

end
end MeasureTheory
