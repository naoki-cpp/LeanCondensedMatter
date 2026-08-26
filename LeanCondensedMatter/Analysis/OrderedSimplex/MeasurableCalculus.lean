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

open Filter Function IsUnifLocDoublingMeasure MeasureTheory Set

/-- Banach-valued Lebesgue differentiation for indefinite interval integrals.  Mathlib v4.31.0 only
exports the real-valued specialization of this statement; the underlying Vitali differentiation
result is already Banach-valued. -/
private theorem ae_hasDerivAt_intervalIntegral_of_locallyIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hLDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have hSetIntegral {a b : ℝ} : ∫ t in Ioc a b, f t = ∫ t in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [hLDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := hy.le
    suffices -((y - x)⁻¹ • ∫ t in Icc y x, f t) =
        (x - y)⁻¹ • ∫ t in Icc y x, f t by
      simpa [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, hSetIntegral]
    rw [← neg_smul, neg_inv, neg_sub]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := hy.le
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
      intervalIntegral.integral_of_le, hy, hSetIntegral]

/-- Local Banach-valued Lebesgue differentiation theorem for an interval-integrable function. -/
theorem ae_hasDerivAt_intervalIntegral_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x, x ∈ uIcc a b → ∀ c ∈ uIcc a b,
      HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards [ae_hasDerivAt_intervalIntegral_of_locallyIntegrable hg, h₁, h₂]
    with x hx _ _ _
  intro c hc
  refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_ <|
    Ioo_mem_nhds (by grind) (by grind)
  rw [show f x = g x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind

/-- A bounded interval-integrable Banach-valued function has an absolutely continuous indefinite
interval integral. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → E} {a b c C : ℝ}
    (hh : IntervalIntegrable h volume a b)
    (hc : c ∈ Set.uIcc a b) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Set.uIcc a b, ‖h t‖ ≤ C) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, h t) a b := by
  let K : NNReal := ⟨C, hC⟩
  have hLip : LipschitzOnWith K (fun x => ∫ t in c..x, h t) (Set.uIcc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
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
      _ = C * dist x y := by rw [Real.dist_eq]
      _ = (K : ℝ) * dist x y := by rfl
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
  let G : ℝ → ℂ := F - fun x => ∫ t in a..x, F' t
  have hG : AbsolutelyContinuousOnInterval G a b := hF.sub hprim
  have hAeInt :
      ∀ᵐ x, x ∈ Set.uIcc a b → ∀ c ∈ Set.uIcc a b,
        HasDerivAt (fun y => ∫ t in c..y, F' t) (F' x) x :=
    ae_hasDerivAt_intervalIntegral_of_intervalIntegrable hF'
  have hGzero : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt G 0 x := by
    filter_upwards [hderiv, hAeInt] with x hxF hxInt hx
    have hInt := hxInt hx a (by simp)
    simpa [G] using (hxF hx).sub hInt
  obtain ⟨D, hD⟩ := hG.const_of_ae_hasDerivAt_zero hGzero
  have hzero : (∫ x in a..a, F' x) = 0 := by simp
  have hGab : F b - (∫ x in a..b, F' x) = F a := by
    have h := (hD b (by simp)).trans (hD a (by simp)).symm
    simpa only [G, Pi.sub_apply, hzero, sub_zero] using h
  calc
    (∫ x in a..b, F' x) = F b - (F b - ∫ x in a..b, F' x) := by abel
    _ = F b - F a := by rw [hGab]

end intervalIntegral
