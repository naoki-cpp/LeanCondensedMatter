import LeanCondensedMatter.Transport.Analysis.LorentzianKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Regular-factor extraction for a Lorentzian pole

This module packages the model-independent analytic core behind isolated-pole Kubo–Bastin limits.
For a complex regular factor `F(offset, broadening)`, a fixed positive symmetric window, joint
continuity at the pole, continuity of the fixed-broadening slices on that window, and a uniform
rectangle bound on the deviation from the pole value imply

```text
∫ L_η(x) F(x, η) dx  →  π F(0, 0)
```

as `η → 0⁺`.

The proof uses only ordinary Mathlib continuity/integrability/norm hypotheses together with the
Lorentzian mass and nested-window tail theorems from `LorentzianKernel`.  It does not mention bands,
Hamiltonians, current operators, occupations, conductivity conventions, or any concrete model.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter MeasureTheory

/-- Lorentzian-weighted fixed-window integral of a complex regular factor. -/
noncomputable def lorentzianRegularFactorIntegral
    (factor : ℝ × ℝ → ℂ) (radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    (lorentzianSpectralKernel offset broadening : ℂ) * factor (offset, broadening)

private noncomputable def lorentzianRegularFactorError
    (factor : ℝ × ℝ → ℂ) (offset broadening : ℝ) : ℂ :=
  factor (offset, broadening) - factor (0, 0)

private noncomputable def lorentzianRegularFactorErrorIntegrand
    (factor : ℝ × ℝ → ℂ) (broadening offset : ℝ) : ℂ :=
  (lorentzianSpectralKernel offset broadening : ℂ) *
    lorentzianRegularFactorError factor offset broadening

private noncomputable def lorentzianRegularFactorErrorIntegral
    (factor : ℝ × ℝ → ℂ) (radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    lorentzianRegularFactorErrorIntegrand factor broadening offset

private noncomputable def lorentzianRegularFactorOuterErrorIntegral
    (factor : ℝ × ℝ → ℂ)
    (innerRadius outerRadius broadening : ℝ) : ℂ :=
  (∫ offset in -outerRadius..-innerRadius,
      lorentzianRegularFactorErrorIntegrand factor broadening offset) +
    ∫ offset in innerRadius..outerRadius,
      lorentzianRegularFactorErrorIntegrand factor broadening offset

/-- For nonzero broadening the Lorentzian kernel is continuous as a function of energy offset. -/
theorem continuous_lorentzianSpectralKernel_fixed_broadening
    (broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (fun offset : ℝ => lorentzianSpectralKernel offset broadening) := by
  have hden : ∀ offset : ℝ, broadening ^ 2 + offset ^ 2 ≠ 0 := by
    intro offset
    nlinarith [sq_pos_of_ne_zero hbroadening]
  unfold lorentzianSpectralKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2)) hden

/-- At nonzero broadening the Lorentzian kernel is interval integrable on every finite interval. -/
theorem intervalIntegrable_lorentzianSpectralKernel
    (lower upper broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IntervalIntegrable (fun offset : ℝ => lorentzianSpectralKernel offset broadening)
      MeasureTheory.volume lower upper := by
  exact (continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening).intervalIntegrable
    (μ := MeasureTheory.volume) lower upper

/-- Every symmetric Lorentzian mass is strictly smaller than `π`. -/
theorem integral_lorentzianSpectralKernel_symmetric_lt_pi
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius,
      lorentzianSpectralKernel offset broadening) < Real.pi := by
  rw [integral_lorentzianSpectralKernel_symmetric]
  linarith [Real.arctan_lt_pi_div_two (radius / broadening)]

private theorem exists_delta_norm_regularFactor_sub_pole_lt_of_coordinates
    (factor : ℝ × ℝ → ℂ) (ε : ℝ)
    (hcontinuous : ContinuousAt factor (0, 0)) (hε : 0 < ε) :
    ∃ δ > 0, ∀ offset broadening : ℝ,
      |offset| < δ → |broadening| < δ →
        ‖factor (offset, broadening) - factor (0, 0)‖ < ε := by
  rw [Metric.continuousAt_iff] at hcontinuous
  rcases hcontinuous ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro offset broadening hoffset hbroadening
  have hdist : dist (offset, broadening) (0, 0) < δ := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt hoffset hbroadening
  have h := hclose hdist
  simpa [dist_eq_norm] using h

private theorem continuousOn_lorentzianRegularFactorErrorIntegrand
    (factor : ℝ × ℝ → ℂ) (radius broadening : ℝ)
    (hslice : ContinuousOn (fun offset : ℝ => factor (offset, broadening))
      (Set.Icc (-radius) radius))
    (hbroadening : broadening ≠ 0) :
    ContinuousOn
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      (Set.Icc (-radius) radius) := by
  have hkernelReal :=
    continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening
  have hkernelComplex : Continuous
      (fun offset : ℝ => (lorentzianSpectralKernel offset broadening : ℂ)) :=
    Complex.continuous_ofReal.comp hkernelReal
  have herror : ContinuousOn
      (fun offset : ℝ => factor (offset, broadening) - factor (0, 0))
      (Set.Icc (-radius) radius) :=
    hslice.sub continuousOn_const
  unfold lorentzianRegularFactorErrorIntegrand lorentzianRegularFactorError
  exact hkernelComplex.continuousOn.mul herror

private theorem intervalIntegrable_lorentzianRegularFactorErrorIntegrand
    (factor : ℝ × ℝ → ℂ) (radius broadening : ℝ)
    (hradius : 0 ≤ radius)
    (hslice : ContinuousOn (fun offset : ℝ => factor (offset, broadening))
      (Set.Icc (-radius) radius))
    (hbroadening : broadening ≠ 0) :
    IntervalIntegrable
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      MeasureTheory.volume (-radius) radius := by
  have hab : -radius ≤ radius := by linarith
  exact
    (continuousOn_lorentzianRegularFactorErrorIntegrand
      factor radius broadening hslice hbroadening).intervalIntegrable_of_Icc hab

private theorem norm_lorentzian_mul_regularFactorError_le
    (factor : ℝ × ℝ → ℂ) (offset broadening tolerance : ℝ)
    (hbroadening : 0 ≤ broadening)
    (herror : ‖lorentzianRegularFactorError factor offset broadening‖ ≤ tolerance) :
    ‖(lorentzianSpectralKernel offset broadening : ℂ) *
        lorentzianRegularFactorError factor offset broadening‖ ≤
      tolerance * lorentzianSpectralKernel offset broadening := by
  have hkernel := lorentzianSpectralKernel_nonneg offset broadening hbroadening
  have hnorm :
      ‖(lorentzianSpectralKernel offset broadening : ℂ)‖ =
        lorentzianSpectralKernel offset broadening := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkernel]
  rw [norm_mul, hnorm]
  calc
    lorentzianSpectralKernel offset broadening *
        ‖lorentzianRegularFactorError factor offset broadening‖ ≤
      lorentzianSpectralKernel offset broadening * tolerance :=
        mul_le_mul_of_nonneg_left herror hkernel
    _ = tolerance * lorentzianSpectralKernel offset broadening := by ring

private theorem norm_integral_lorentzian_mul_regularFactorError_le
    (factor : ℝ × ℝ → ℂ) (innerRadius broadening tolerance : ℝ)
    (hinner : 0 ≤ innerRadius) (hbroadening : 0 < broadening)
    (herror : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖lorentzianRegularFactorError factor offset broadening‖ ≤ tolerance) :
    ‖∫ offset in -innerRadius..innerRadius,
        lorentzianRegularFactorErrorIntegrand factor broadening offset‖ ≤
      tolerance *
        (∫ offset in -innerRadius..innerRadius,
          lorentzianSpectralKernel offset broadening) := by
  have hab : -innerRadius ≤ innerRadius := by linarith
  have hkernelInt := intervalIntegrable_lorentzianSpectralKernel
    (-innerRadius) innerRadius broadening hbroadening.ne'
  have hineq :
      ‖∫ offset in -innerRadius..innerRadius,
          lorentzianRegularFactorErrorIntegrand factor broadening offset‖ ≤
        ∫ offset in -innerRadius..innerRadius,
          tolerance * lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_regularFactorError_le
        factor offset broadening tolerance hbroadening.le
      apply herror offset
      exact abs_le.mpr ⟨le_of_lt hoffset.1, hoffset.2⟩
    · exact hkernelInt.const_mul tolerance
  rw [intervalIntegral.integral_const_mul] at hineq
  exact hineq

private def lorentzianSpectralOuterMass
    (innerRadius outerRadius broadening : ℝ) : ℝ :=
  (∫ offset in -outerRadius..-innerRadius,
      lorentzianSpectralKernel offset broadening) +
    ∫ offset in innerRadius..outerRadius,
      lorentzianSpectralKernel offset broadening

private theorem lorentzianSpectralOuterMass_eq_tailMass
    (innerRadius outerRadius broadening : ℝ) (hbroadening : broadening ≠ 0) :
    lorentzianSpectralOuterMass innerRadius outerRadius broadening =
      lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  have hleft := intervalIntegrable_lorentzianSpectralKernel
    (-outerRadius) (-innerRadius) broadening hbroadening
  have hmiddle := intervalIntegrable_lorentzianSpectralKernel
    (-innerRadius) innerRadius broadening hbroadening
  have hright := intervalIntegrable_lorentzianSpectralKernel
    innerRadius outerRadius broadening hbroadening
  have hwhole := intervalIntegral.integral_add_adjacent_intervals
    (hleft.trans hmiddle) hright
  have hleftMiddle := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  unfold lorentzianSpectralOuterMass lorentzianSpectralTailMass
  linarith

private theorem norm_lorentzianRegularFactorOuterErrorIntegral_le
    (factor : ℝ × ℝ → ℂ)
    (innerRadius outerRadius broadening C : ℝ)
    (hinner : 0 ≤ innerRadius) (hnested : innerRadius ≤ outerRadius)
    (hbroadening : 0 < broadening)
    (herror : ∀ offset : ℝ, innerRadius ≤ |offset| → |offset| ≤ outerRadius →
      ‖lorentzianRegularFactorError factor offset broadening‖ ≤ C) :
    ‖lorentzianRegularFactorOuterErrorIntegral
        factor innerRadius outerRadius broadening‖ ≤
      C * lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  have hleftOrder : -outerRadius ≤ -innerRadius := by linarith
  have hrightOrder : innerRadius ≤ outerRadius := hnested
  have hleftKernel := intervalIntegrable_lorentzianSpectralKernel
    (-outerRadius) (-innerRadius) broadening hbroadening.ne'
  have hrightKernel := intervalIntegrable_lorentzianSpectralKernel
    innerRadius outerRadius broadening hbroadening.ne'
  have hleftBound :
      ‖∫ offset in -outerRadius..-innerRadius,
          lorentzianRegularFactorErrorIntegrand factor broadening offset‖ ≤
        ∫ offset in -outerRadius..-innerRadius,
          C * lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hleftOrder
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_regularFactorError_le
        factor offset broadening C hbroadening.le
      have hoffsetNonpos : offset ≤ 0 := by linarith [hoffset.2]
      apply herror offset
      · rw [abs_of_nonpos hoffsetNonpos]
        linarith [hoffset.2]
      · rw [abs_of_nonpos hoffsetNonpos]
        linarith [hoffset.1]
    · exact hleftKernel.const_mul C
  have hrightBound :
      ‖∫ offset in innerRadius..outerRadius,
          lorentzianRegularFactorErrorIntegrand factor broadening offset‖ ≤
        ∫ offset in innerRadius..outerRadius,
          C * lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hrightOrder
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_regularFactorError_le
        factor offset broadening C hbroadening.le
      have hoffsetNonneg : 0 ≤ offset := by linarith [hoffset.1]
      apply herror offset
      · rw [abs_of_nonneg hoffsetNonneg]
        linarith [hoffset.1]
      · rw [abs_of_nonneg hoffsetNonneg]
        exact hoffset.2
    · exact hrightKernel.const_mul C
  calc
    ‖lorentzianRegularFactorOuterErrorIntegral
        factor innerRadius outerRadius broadening‖ ≤
        ‖∫ offset in -outerRadius..-innerRadius,
            lorentzianRegularFactorErrorIntegrand factor broadening offset‖ +
          ‖∫ offset in innerRadius..outerRadius,
            lorentzianRegularFactorErrorIntegrand factor broadening offset‖ := by
      exact norm_add_le _ _
    _ ≤ (∫ offset in -outerRadius..-innerRadius,
          C * lorentzianSpectralKernel offset broadening) +
        ∫ offset in innerRadius..outerRadius,
          C * lorentzianSpectralKernel offset broadening :=
      add_le_add hleftBound hrightBound
    _ = C * lorentzianSpectralOuterMass innerRadius outerRadius broadening := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      unfold lorentzianSpectralOuterMass
      ring
    _ = C * lorentzianSpectralTailMass innerRadius outerRadius broadening := by
      rw [lorentzianSpectralOuterMass_eq_tailMass innerRadius outerRadius broadening
        hbroadening.ne']

private theorem lorentzianRegularFactorErrorIntegral_eq_outer_add_inner
    (factor : ℝ × ℝ → ℂ)
    (innerRadius outerRadius broadening : ℝ)
    (hinner : 0 ≤ innerRadius) (hnested : innerRadius ≤ outerRadius)
    (hbroadening : broadening ≠ 0)
    (hslice : ContinuousOn (fun offset : ℝ => factor (offset, broadening))
      (Set.Icc (-outerRadius) outerRadius)) :
    lorentzianRegularFactorErrorIntegral factor outerRadius broadening =
      lorentzianRegularFactorOuterErrorIntegral
          factor innerRadius outerRadius broadening +
        (∫ offset in -innerRadius..innerRadius,
          lorentzianRegularFactorErrorIntegrand factor broadening offset) := by
  have houterNonneg : 0 ≤ outerRadius := le_trans hinner hnested
  have hcont := continuousOn_lorentzianRegularFactorErrorIntegrand
    factor outerRadius broadening hslice hbroadening
  have hleftCont : ContinuousOn
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      (Set.Icc (-outerRadius) (-innerRadius)) := by
    apply hcont.mono
    intro offset hoffset
    constructor
    · exact hoffset.1
    · linarith [hoffset.2]
  have hmiddleCont : ContinuousOn
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      (Set.Icc (-innerRadius) innerRadius) := by
    apply hcont.mono
    intro offset hoffset
    constructor <;> linarith [hoffset.1, hoffset.2]
  have hrightCont : ContinuousOn
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      (Set.Icc innerRadius outerRadius) := by
    apply hcont.mono
    intro offset hoffset
    constructor
    · linarith [hoffset.1]
    · exact hoffset.2
  have hleft : IntervalIntegrable
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      MeasureTheory.volume (-outerRadius) (-innerRadius) := by
    exact hleftCont.intervalIntegrable_of_Icc (by linarith)
  have hmiddle : IntervalIntegrable
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      MeasureTheory.volume (-innerRadius) innerRadius := by
    exact hmiddleCont.intervalIntegrable_of_Icc (by linarith)
  have hright : IntervalIntegrable
      (lorentzianRegularFactorErrorIntegrand factor broadening)
      MeasureTheory.volume innerRadius outerRadius := by
    exact hrightCont.intervalIntegrable_of_Icc hnested
  have hleftMiddle := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hwhole := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  unfold lorentzianRegularFactorErrorIntegral
  rw [← hwhole, ← hleftMiddle]
  unfold lorentzianRegularFactorOuterErrorIntegral
  ring

private theorem tendsto_lorentzianRegularFactorErrorIntegral_zero
    (factor : ℝ × ℝ → ℂ) (radius : ℝ)
    (hradiusPos : 0 < radius)
    (hcontinuous : ContinuousAt factor (0, 0))
    (hslice : ∀ broadening : ℝ, broadening ≠ 0 →
      ContinuousOn (fun offset : ℝ => factor (offset, broadening))
        (Set.Icc (-radius) radius))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1,
        ‖factor p - factor (0, 0)‖ ≤ C) :
    Tendsto
      (fun broadening : ℝ =>
        lorentzianRegularFactorErrorIntegral factor radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  rcases hbound with ⟨C, hCnonneg, hC⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  let tolerance : ℝ := ε / (4 * (Real.pi + 1))
  have hpiOnePos : 0 < Real.pi + 1 := by positivity
  have htolerancePos : 0 < tolerance := by
    dsimp [tolerance]
    positivity
  rcases exists_delta_norm_regularFactor_sub_pole_lt_of_coordinates
      factor tolerance hcontinuous htolerancePos with ⟨δ, hδ, hlocal⟩
  let innerRadius : ℝ := min (radius / 2) (δ / 2)
  have hinnerPos : 0 < innerRadius := by
    dsimp [innerRadius]
    exact lt_min_iff.mpr ⟨half_pos hradiusPos, half_pos hδ⟩
  have hinnerNonneg : 0 ≤ innerRadius := hinnerPos.le
  have hnested : innerRadius ≤ radius := by
    dsimp [innerRadius]
    calc
      min (radius / 2) (δ / 2) ≤ radius / 2 := min_le_left _ _
      _ ≤ radius := by linarith
  have hinnerLtDelta : innerRadius < δ := by
    dsimp [innerRadius]
    calc
      min (radius / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith
  let etaRadius : ℝ := min δ 1
  have hetaRadiusPos : 0 < etaRadius := by
    dsimp [etaRadius]
    exact lt_min_iff.mpr ⟨hδ, zero_lt_one⟩
  have hwithin_le : nhdsWithin 0 (Set.Ioi 0) ≤ nhds (0 : ℝ) := by
    exact inf_le_left
  have hetaSmall : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      broadening < etaRadius :=
    hwithin_le (Iio_mem_nhds hetaRadiusPos)
  have hetaPos : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < broadening := by
    change Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0)
    exact self_mem_nhdsWithin
  let tailTolerance : ℝ := ε / (4 * (C + 1))
  have hCOnePos : 0 < C + 1 := by linarith
  have htailTolerancePos : 0 < tailTolerance := by
    dsimp [tailTolerance]
    exact div_pos hε (mul_pos (by norm_num) hCOnePos)
  have htail := tendsto_lorentzianSpectralTailMass_zero
    innerRadius radius hinnerPos hnested
  have htailClose : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      dist (lorentzianSpectralTailMass innerRadius radius broadening) 0 <
        tailTolerance :=
    (Metric.tendsto_nhds.1 htail) tailTolerance htailTolerancePos
  filter_upwards [hetaPos, hetaSmall, htailClose] with broadening hbroadening hsmall htailCloseAt
  have hbroadeningLtDelta : broadening < δ := by
    exact lt_of_lt_of_le hsmall (min_le_left _ _)
  have hbroadeningLtOne : broadening < 1 := by
    exact lt_of_lt_of_le hsmall (min_le_right _ _)
  have hlocalAt : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖lorentzianRegularFactorError factor offset broadening‖ ≤ tolerance := by
    intro offset hoffset
    have hoffsetLtDelta : |offset| < δ := lt_of_le_of_lt hoffset hinnerLtDelta
    have hbroadeningAbsLtDelta : |broadening| < δ := by
      simpa [abs_of_pos hbroadening] using hbroadeningLtDelta
    have h := hlocal offset broadening hoffsetLtDelta hbroadeningAbsLtDelta
    simpa [lorentzianRegularFactorError] using h.le
  have hannulusAt : ∀ offset : ℝ,
      innerRadius ≤ |offset| → |offset| ≤ radius →
      ‖lorentzianRegularFactorError factor offset broadening‖ ≤ C := by
    intro offset _ hoffsetOuter
    apply hC (offset, broadening)
    refine ⟨abs_le.mp hoffsetOuter, ?_⟩
    exact ⟨hbroadening.le, hbroadeningLtOne.le⟩
  have hsplit := lorentzianRegularFactorErrorIntegral_eq_outer_add_inner
    factor innerRadius radius broadening hinnerNonneg hnested hbroadening.ne'
      (hslice broadening hbroadening.ne')
  have hboundAt :
      ‖lorentzianRegularFactorErrorIntegral factor radius broadening‖ ≤
        tolerance *
            (∫ offset in -innerRadius..innerRadius,
              lorentzianSpectralKernel offset broadening) +
          C * lorentzianSpectralTailMass innerRadius radius broadening := by
    rw [hsplit]
    calc
      ‖lorentzianRegularFactorOuterErrorIntegral
            factor innerRadius radius broadening +
          (∫ offset in -innerRadius..innerRadius,
            lorentzianRegularFactorErrorIntegrand factor broadening offset)‖ ≤
        ‖lorentzianRegularFactorOuterErrorIntegral
            factor innerRadius radius broadening‖ +
          ‖∫ offset in -innerRadius..innerRadius,
            lorentzianRegularFactorErrorIntegrand factor broadening offset‖ :=
        norm_add_le _ _
      _ ≤ C * lorentzianSpectralTailMass innerRadius radius broadening +
          tolerance *
            (∫ offset in -innerRadius..innerRadius,
              lorentzianSpectralKernel offset broadening) := by
        apply add_le_add
        · exact norm_lorentzianRegularFactorOuterErrorIntegral_le
            factor innerRadius radius broadening C hinnerNonneg hnested
            hbroadening hannulusAt
        · exact norm_integral_lorentzian_mul_regularFactorError_le
            factor innerRadius broadening tolerance hinnerNonneg hbroadening hlocalAt
      _ = tolerance *
            (∫ offset in -innerRadius..innerRadius,
              lorentzianSpectralKernel offset broadening) +
          C * lorentzianSpectralTailMass innerRadius radius broadening := by
        ring
  have hmassLtPi :=
    integral_lorentzianSpectralKernel_symmetric_lt_pi innerRadius broadening
  have hinnerTermLt :
      tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) < ε / 4 := by
    have hmassLt :
        (∫ offset in -innerRadius..innerRadius,
          lorentzianSpectralKernel offset broadening) < Real.pi + 1 := by
      linarith
    calc
      tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) <
        tolerance * (Real.pi + 1) :=
          mul_lt_mul_of_pos_left hmassLt htolerancePos
      _ = ε / 4 := by
        dsimp [tolerance]
        field_simp [ne_of_gt hpiOnePos]
  have htailLt :
      lorentzianSpectralTailMass innerRadius radius broadening < tailTolerance := by
    have habs :
        |lorentzianSpectralTailMass innerRadius radius broadening| < tailTolerance := by
      simpa [Real.dist_eq] using htailCloseAt
    exact lt_of_le_of_lt (le_abs_self _) habs
  have houterTermLe :
      C * lorentzianSpectralTailMass innerRadius radius broadening ≤ ε / 4 := by
    calc
      C * lorentzianSpectralTailMass innerRadius radius broadening ≤
          C * tailTolerance :=
        mul_le_mul_of_nonneg_left (le_of_lt htailLt) hCnonneg
      _ ≤ (C + 1) * tailTolerance :=
        mul_le_mul_of_nonneg_right (by linarith) htailTolerancePos.le
      _ = ε / 4 := by
        dsimp [tailTolerance]
        field_simp [ne_of_gt hCOnePos]
  have hnormLt : ‖lorentzianRegularFactorErrorIntegral factor radius broadening‖ < ε := by
    calc
      ‖lorentzianRegularFactorErrorIntegral factor radius broadening‖ ≤
        tolerance *
            (∫ offset in -innerRadius..innerRadius,
              lorentzianSpectralKernel offset broadening) +
          C * lorentzianSpectralTailMass innerRadius radius broadening := hboundAt
      _ < ε / 4 + ε / 4 := add_lt_add_of_lt_of_le hinnerTermLt houterTermLe
      _ < ε := by linarith
  simpa [dist_eq_norm] using hnormLt

private theorem real_smul_complex_eq_mul (r : ℝ) (z : ℂ) :
    r • z = (r : ℂ) * z := by
  rfl

private theorem lorentzianRegularFactorIntegral_eq_error_add_mass_smul_pole
    (factor : ℝ × ℝ → ℂ) (radius broadening : ℝ)
    (hradius : 0 ≤ radius)
    (hbroadening : broadening ≠ 0)
    (hslice : ContinuousOn (fun offset : ℝ => factor (offset, broadening))
      (Set.Icc (-radius) radius)) :
    lorentzianRegularFactorIntegral factor radius broadening =
      lorentzianRegularFactorErrorIntegral factor radius broadening +
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) • factor (0, 0) := by
  have herrorInt := intervalIntegrable_lorentzianRegularFactorErrorIntegrand
    factor radius broadening hradius hslice hbroadening
  have hkernelCont :=
    continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening
  have hpoleInt : IntervalIntegrable
      (fun offset : ℝ =>
        lorentzianSpectralKernel offset broadening • factor (0, 0))
      MeasureTheory.volume (-radius) radius := by
    exact (hkernelCont.smul continuous_const).intervalIntegrable
      (μ := MeasureTheory.volume) (-radius) radius
  unfold lorentzianRegularFactorIntegral
  calc
    (∫ offset in -radius..radius,
        (lorentzianSpectralKernel offset broadening : ℂ) * factor (offset, broadening)) =
      ∫ offset in -radius..radius,
        lorentzianRegularFactorErrorIntegrand factor broadening offset +
          lorentzianSpectralKernel offset broadening • factor (0, 0) := by
        apply intervalIntegral.integral_congr
        intro offset _
        unfold lorentzianRegularFactorErrorIntegrand lorentzianRegularFactorError
        change
          (lorentzianSpectralKernel offset broadening : ℂ) * factor (offset, broadening) =
            (lorentzianSpectralKernel offset broadening : ℂ) *
                (factor (offset, broadening) - factor (0, 0)) +
              lorentzianSpectralKernel offset broadening • factor (0, 0)
        rw [real_smul_complex_eq_mul]
        ring
    _ = (∫ offset in -radius..radius,
          lorentzianRegularFactorErrorIntegrand factor broadening offset) +
        ∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening • factor (0, 0) := by
        exact intervalIntegral.integral_add herrorInt hpoleInt
    _ = lorentzianRegularFactorErrorIntegral factor radius broadening +
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) • factor (0, 0) := by
        unfold lorentzianRegularFactorErrorIntegral
        rw [intervalIntegral.integral_smul_const]

/-- A Lorentzian approximate identity extracts the pole value of any complex regular factor that is
jointly continuous at `(0,0)`, has continuous nonzero-broadening slices on the fixed symmetric
window, and has a uniform bound on its deviation from the pole value over that window for
`0 ≤ broadening ≤ 1`. -/
theorem tendsto_lorentzianRegularFactorIntegral
    (factor : ℝ × ℝ → ℂ) (radius : ℝ)
    (hradiusPos : 0 < radius)
    (hcontinuous : ContinuousAt factor (0, 0))
    (hslice : ∀ broadening : ℝ, broadening ≠ 0 →
      ContinuousOn (fun offset : ℝ => factor (offset, broadening))
        (Set.Icc (-radius) radius))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1,
        ‖factor p - factor (0, 0)‖ ≤ C) :
    Tendsto
      (fun broadening : ℝ =>
        lorentzianRegularFactorIntegral factor radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi • factor (0, 0))) := by
  have herror := tendsto_lorentzianRegularFactorErrorIntegral_zero
    factor radius hradiusPos hcontinuous hslice hbound
  have hmass := tendsto_integral_lorentzianSpectralKernel_symmetric radius hradiusPos
  have hsmulContinuous : ContinuousAt
      (fun mass : ℝ => mass • factor (0, 0)) Real.pi := by
    fun_prop
  have hmassPole : Tendsto
      (fun broadening : ℝ =>
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) • factor (0, 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi • factor (0, 0))) := by
    exact hsmulContinuous.tendsto.comp hmass
  have hsum : Tendsto
      (fun broadening : ℝ =>
        lorentzianRegularFactorErrorIntegral factor radius broadening +
          (∫ offset in -radius..radius,
            lorentzianSpectralKernel offset broadening) • factor (0, 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi • factor (0, 0))) := by
    simpa using herror.add hmassPole
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hclose := (Metric.tendsto_nhds.1 hsum) ε hε
  have hpositive : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < broadening := by
    change Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hpositive, hclose] with broadening hbroadening hcloseAt
  rw [lorentzianRegularFactorIntegral_eq_error_add_mass_smul_pole
    factor radius broadening hradiusPos.le hbroadening.ne'
      (hslice broadening hbroadening.ne')]
  exact hcloseAt

end

end Transport
end QuantumTheory
