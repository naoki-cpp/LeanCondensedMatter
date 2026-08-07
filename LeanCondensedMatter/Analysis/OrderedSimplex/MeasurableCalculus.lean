import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

set_option linter.style.header false

/-!
# Absolute-continuity calculus for bounded measurable ordered-simplex primitives

The continuous shuffle proof differentiates ordered-simplex primitives pointwise.  For the actual
component factors we only have measurable local boundedness.  On every finite interval the exposed
boundary integrand is interval integrable and uniformly bounded, so its indefinite Bochner integral
is Lipschitz, hence absolutely continuous.  This is enough to recover the fundamental theorem of
calculus from an a.e. derivative without restoring a false global-continuity hypothesis.
-/

namespace intervalIntegral

open Filter MeasureTheory Set

/-- A bounded interval-integrable Banach-valued function has an absolutely continuous indefinite
interval integral. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : ℝ → E} {a b c C : ℝ}
    (hh : IntervalIntegrable h volume a b)
    (hc : c ∈ Set.uIcc a b) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Set.uIcc a b, ‖h t‖ ≤ C) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, h t) a b := by
  let K : NNReal := ⟨C, hC⟩
  have hLip : LipschitzOnWith K (fun x => ∫ t in c..x, h t) (Set.uIcc a b) := by
    intro x hx y hy
    rw [dist_eq_norm]
    have hcx : IntervalIntegrable h volume c x := by
      apply hh.mono_set'
      grind [Set.uIoc, Set.uIcc]
    have hcy : IntervalIntegrable h volume c y := by
      apply hh.mono_set'
      grind [Set.uIoc, Set.uIcc]
    rw [intervalIntegral.integral_interval_sub_left hcx hcy]
    calc
      ‖∫ t in y..x, h t‖ ≤ C * |x - y| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        apply hbound
        grind [Set.uIoc, Set.uIcc]
      _ = (K : ℝ) * dist x y := by
        simp [K, Real.dist_eq, abs_sub_comm]
  exact hLip.absolutelyContinuousOnInterval

/-- Fundamental theorem of calculus for an absolutely continuous complex-valued primitive with a
specified a.e. derivative.  The derivative is assumed bounded only to construct the absolutely
continuous Bochner primitive used in the standard zero-derivative argument. -/
theorem integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt_of_norm_le
    {F F' : ℝ → ℂ} {a b C : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hF' : IntervalIntegrable F' volume a b)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Set.uIcc a b, ‖F' x‖ ≤ C)
    (hderiv : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt F (F' x) x) :
    (∫ x in a..b, F' x) = F b - F a := by
  have hprim : AbsolutelyContinuousOnInterval (fun x => ∫ t in a..x, F' t) a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
      hF' (by simp) hC hbound
  let G : ℝ → ℂ := fun x => F x - ∫ t in a..x, F' t
  have hG : AbsolutelyContinuousOnInterval G a b := hF.sub hprim
  have hAeInt := IntervalIntegrable.ae_hasDerivAt_integral (f := F') hF'
  have hGzero : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt G 0 x := by
    filter_upwards [hderiv, hAeInt] with x hxF hxInt hx
    have hInt := hxInt hx a (by simp)
    simpa [G] using (hxF hx).sub hInt
  obtain ⟨D, hD⟩ := hG.const_of_ae_hasDerivAt_zero hGzero
  have ha := hD a (by simp)
  have hb := hD b (by simp)
  simp [G] at ha hb
  rw [← ha] at hb
  calc
    (∫ x in a..b, F' x) = F b - (F b - ∫ x in a..b, F' x) := by abel
    _ = F b - F a := by rw [hb]

end intervalIntegral
