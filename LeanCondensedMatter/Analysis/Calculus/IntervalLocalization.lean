import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Full-line localization of oriented interval integrals

Mathlib's `intervalIntegral` already carries the orientation of an integral from `a` to `b`. This
module supplies the complementary full-line realization used by downstream energy-kernel
constructions: the integrand on `(a, b]` minus the integrand on `(b, a]`.

The construction is representation-independent and contains no transport assumptions.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory Set

noncomputable section

/-- A full-line function encoding the oriented interval integral from `a` to `b`. -/
noncomputable def orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b energy : ℝ) : ℂ :=
  (Ioc a b).indicator f energy - (Ioc b a).indicator f energy

theorem integrable_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    Integrable (orientedIntervalIntegrand f a b) := by
  unfold orientedIntervalIntegrand
  exact (hf.1.integrable_indicator measurableSet_Ioc).sub
    (hf.2.integrable_indicator measurableSet_Ioc)

theorem integral_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
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
end Transport
end QuantumTheory
