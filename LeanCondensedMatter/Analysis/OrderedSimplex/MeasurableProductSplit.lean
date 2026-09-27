import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

set_option linter.style.header false

/-!
# Product split for measurable locally bounded ordered-simplex integrands

For measurable locally bounded ordered-simplex integrands, exposed boundary terms are interval
integrable and uniformly bounded on finite intervals. Their indefinite Bochner integrals are
therefore absolutely continuous, and Banach-valued Lebesgue differentiation supplies the a.e.
derivatives needed for the fundamental theorem of calculus. These internal calculus facts yield the
positive-dimensional product split without imposing a false global-continuity hypothesis.
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
private theorem ae_hasDerivAt_intervalIntegral_of_intervalIntegrable
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
private theorem absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
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
private theorem integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt_of_norm_le
    {F F' : ℝ → ℂ} {a b C : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hF' : IntervalIntegrable F' volume a b)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Set.uIcc a b, ‖F' x‖ ≤ C)
    (hderiv : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt F (F' x) x) :
    (∫ x in a..b, F' x) = F b - F a := by
  have hprim : AbsolutelyContinuousOnInterval (fun x => ∫ t in a..x, F' t) a b :=
    absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
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


/-- Split a product of two positive-dimensional ordered-simplex integrals under measurable local
boundedness, with no global continuity assumption on either raw integrand. -/
theorem orderedSimplexIntegral_succ_mul_succ_of_measurableLocallyBounded
    (m n : ℕ) (β : ℝ)
    (f : (Fin (m + 1) → ℝ) → ℂ) (g : (Fin (n + 1) → ℝ) → ℂ)
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    orderedSimplexIntegral (m + 1) β f * orderedSimplexIntegral (n + 1) β g =
      ∫ t in (0 : ℝ)..β,
        orderedSimplexIntegral m t (fun rest => f (Fin.cons t rest)) *
            orderedSimplexIntegral (n + 1) t g +
          orderedSimplexIntegral (m + 1) t f *
            orderedSimplexIntegral n t (fun rest => g (Fin.cons t rest)) := by
  let u : ℝ → ℂ := fun t => orderedSimplexIntegral (m + 1) t f
  let v : ℝ → ℂ := fun t => orderedSimplexIntegral (n + 1) t g
  let u' : ℝ → ℂ := fun t =>
    orderedSimplexIntegral m t (fun rest => f (Fin.cons t rest))
  let v' : ℝ → ℂ := fun t =>
    orderedSimplexIntegral n t (fun rest => g (Fin.cons t rest))
  have huInt : IntervalIntegrable u' volume 0 β := by
    simpa [u'] using hf.intervalIntegrable_orderedSimplexIntegral_boundary β
  have hvInt : IntervalIntegrable v' volume 0 β := by
    simpa [v'] using hg.intervalIntegrable_orderedSimplexIntegral_boundary β
  obtain ⟨Du, hDu0, hDu⟩ := hf.exists_norm_bound_orderedSimplexIntegral_boundary β
  obtain ⟨Dv, hDv0, hDv⟩ := hg.exists_norm_bound_orderedSimplexIntegral_boundary β
  have hDu' : ∀ t ∈ Set.uIcc (0 : ℝ) β, ‖u' t‖ ≤ Du := by
    simpa [u'] using hDu
  have hDv' : ∀ t ∈ Set.uIcc (0 : ℝ) β, ‖v' t‖ ≤ Dv := by
    simpa [v'] using hDv
  have huAC : AbsolutelyContinuousOnInterval u 0 β := by
    have h :=
      absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
        huInt (c := (0 : ℝ)) (by simp) hDu0 hDu'
    simpa [u, u', orderedSimplexIntegral_succ] using h
  have hvAC : AbsolutelyContinuousOnInterval v 0 β := by
    have h :=
      absolutelyContinuousOnInterval_intervalIntegral_of_norm_le
        hvInt (c := (0 : ℝ)) (by simp) hDv0 hDv'
    simpa [v, v', orderedSimplexIntegral_succ] using h
  have huAeInt := ae_hasDerivAt_intervalIntegral_of_intervalIntegrable huInt
  have hvAeInt := ae_hasDerivAt_intervalIntegral_of_intervalIntegrable hvInt
  have huDeriv : ∀ᵐ t, t ∈ Set.uIcc (0 : ℝ) β → HasDerivAt u (u' t) t := by
    filter_upwards [huAeInt] with t ht hmem
    have h := ht hmem 0 (by simp)
    simpa [u, u', orderedSimplexIntegral_succ] using h
  have hvDeriv : ∀ᵐ t, t ∈ Set.uIcc (0 : ℝ) β → HasDerivAt v (v' t) t := by
    filter_upwards [hvAeInt] with t ht hmem
    have h := ht hmem 0 (by simp)
    simpa [v, v', orderedSimplexIntegral_succ] using h
  let w : ℝ → ℂ := fun t => u t * v t
  let w' : ℝ → ℂ := fun t => u' t * v t + u t * v' t
  have hwAC : AbsolutelyContinuousOnInterval w 0 β := by
    change AbsolutelyContinuousOnInterval (u • v) 0 β
    exact huAC.smul hvAC
  have hwDeriv : ∀ᵐ t, t ∈ Set.uIcc (0 : ℝ) β → HasDerivAt w (w' t) t := by
    filter_upwards [huDeriv, hvDeriv] with t hut hvt ht
    exact (hut ht).mul (hvt ht)
  have hwInt : IntervalIntegrable w' volume 0 β := by
    have hleft : IntervalIntegrable (fun t => u' t * v t) volume 0 β :=
      huInt.mul_continuousOn hvAC.continuousOn
    have hright : IntervalIntegrable (fun t => u t * v' t) volume 0 β :=
      hvInt.continuousOn_mul huAC.continuousOn
    exact hleft.add hright
  obtain ⟨U, hU⟩ := huAC.exists_bound
  obtain ⟨V, hV⟩ := hvAC.exists_bound
  let U₀ := max U 0
  let V₀ := max V 0
  have hU₀ : 0 ≤ U₀ := le_max_right _ _
  have hV₀ : 0 ≤ V₀ := le_max_right _ _
  have huBound : ∀ t ∈ Set.uIcc (0 : ℝ) β, ‖u t‖ ≤ U₀ := by
    intro t ht
    exact (hU t ht).trans (le_max_left _ _)
  have hvBound : ∀ t ∈ Set.uIcc (0 : ℝ) β, ‖v t‖ ≤ V₀ := by
    intro t ht
    exact (hV t ht).trans (le_max_left _ _)
  let D := Du * V₀ + U₀ * Dv
  have hD : 0 ≤ D := add_nonneg (mul_nonneg hDu0 hV₀) (mul_nonneg hU₀ hDv0)
  have hwBound : ∀ t ∈ Set.uIcc (0 : ℝ) β, ‖w' t‖ ≤ D := by
    intro t ht
    calc
      ‖w' t‖ ≤ ‖u' t * v t‖ + ‖u t * v' t‖ := by
        simpa [w'] using norm_add_le (u' t * v t) (u t * v' t)
      _ = ‖u' t‖ * ‖v t‖ + ‖u t‖ * ‖v' t‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ Du * V₀ + U₀ * Dv := by
        gcongr
        · exact hDu' t ht
        · exact hvBound t ht
        · exact huBound t ht
        · exact hDv' t ht
      _ = D := rfl
  have hFTC :=
    integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt_of_norm_le
      hwAC hwInt hD hwBound hwDeriv
  have hu0 : u 0 = 0 := by simp [u, orderedSimplexIntegral_succ]
  have hv0 : v 0 = 0 := by simp [v, orderedSimplexIntegral_succ]
  change u β * v β = ∫ t in (0 : ℝ)..β, w' t
  rw [hFTC]
  simp [w, hu0, hv0]

end intervalIntegral
