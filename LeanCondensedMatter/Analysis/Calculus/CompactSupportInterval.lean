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

/-- A strict threshold truncates the integral at an interior cut. The value at the
cut itself does not matter for Lebesgue integration. -/
theorem integral_strictThreshold_mul {a b c : ℝ} (f : ℝ → ℝ)
    (ha : a ≤ c) (hb : c ≤ b) :
    (∫ x in a..b, (if x < c then 1 else 0) * f x) =
      ∫ x in a..c, f x := by
  calc
    (∫ x in a..b, (if x < c then 1 else 0) * f x) =
        ∫ x in a..b, Set.indicator {x : ℝ | x ≤ c} f x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne c] with x hne
      intro _
      by_cases hlt : x < c
      · simp [hlt, hlt.le]
      · have hgt : c < x := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
        simp [hlt, not_le.mpr hgt]
    _ = ∫ x in a..c, f x := intervalIntegral.integral_indicator ⟨ha, hb⟩


/-- A pairing that vanishes when its first argument is zero has the same interval
and full-line integrals if the first argument is supported inside the interval.
No continuity or integrability assertion is needed for this equality of total integrals. -/
theorem integral_pairing_eq_integral_of_tsupport_subset_Ioo
    {E F G : Type*} [Zero E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b : ℝ} {f : ℝ → E} {g : ℝ → F}
    (B : E → F → G) (hzero : ∀ y, B 0 y = 0)
    (hf : tsupport f ⊆ Ioo a b) :
    (∫ x in a..b, B (f x) (g x)) = ∫ x, B (f x) (g x) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hfx : x ∈ Function.support f := by
    intro hz
    apply hx
    change B (f x) (g x) = 0
    rw [hz, hzero]
  have h := hf (subset_closure hfx)
  exact ⟨h.1, h.2.le⟩

/-- A function whose topological support is strictly inside an interval vanishes at both
endpoints. -/
theorem endpoint_values_eq_zero_of_tsupport_subset_Ioo
    {E : Type*} [Zero E] {a b : ℝ} {f : ℝ → E}
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
