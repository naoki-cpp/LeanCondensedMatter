import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePoleWeight
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleInnerError
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature occupation-weighted pole-error bound

To lift the scalar zero-temperature pole weight to the regular interband Bastin pair, the only
remaining pointwise issue is the spectator/current factor.  The occupation has norm at most one, so
it never enlarges the local spectator error.

Instead of duplicating the earlier inner/outer interval split, this file uses the elementary second
moment estimate

```text
x² η / (η² + x²) ≤ η.
```

A local continuity bound controls the pole region, while a compact global error bound is multiplied
by `x² / r²` outside a positive inner radius.  The resulting weighted error is bounded by a small
multiple of the full Lorentzian mass plus a term linear in the broadening.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory

/-- Zero-temperature occupation-weighted Lorentzian spectator error on a fixed target window. -/
noncomputable def targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
    (band : Band) (e v m px py fermiEnergy radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    ((zeroTemperatureOccupation fermiEnergy
        (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
      ((lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentError
          band e v m px py offset broadening)

/-- Multiplying by zero-temperature occupation preserves every pointwise Lorentzian spectator-error
bound because the occupation has norm at most one. -/
theorem norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectatorError_le
    (band : Band) (e v m px py fermiEnergy offset broadening tolerance : ℝ)
    (hbroadening : 0 ≤ broadening)
    (herror : ‖targetCenteredInterbandSpectatorCurrentError
      band e v m px py offset broadening‖ ≤ tolerance) :
    ‖((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentError
            band e v m px py offset broadening)‖ ≤
      tolerance * lorentzianSpectralKernel offset broadening := by
  rw [norm_mul]
  calc
    ‖((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m px py + offset) : ℝ) : ℂ)‖ *
        ‖(lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentError
            band e v m px py offset broadening‖ ≤
      1 * ‖(lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentError
            band e v m px py offset broadening‖ := by
        exact mul_le_mul_of_nonneg_right
          (norm_zeroTemperatureOccupation_complex_le_one
            fermiEnergy (bandEnergy band v m px py + offset)) (norm_nonneg _)
    _ = ‖(lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentError
            band e v m px py offset broadening‖ := by ring
    _ ≤ tolerance * lorentzianSpectralKernel offset broadening :=
      norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
        band e v m px py offset broadening tolerance hbroadening herror

/-- The second-moment Lorentzian density used for the global-away-from-pole estimate. -/
def lorentzianSpectralSecondMoment (offset broadening : ℝ) : ℝ :=
  offset ^ 2 * lorentzianSpectralKernel offset broadening

/-- For positive broadening, the Lorentzian second-moment density is pointwise at most the
broadening itself. -/
theorem lorentzianSpectralSecondMoment_le_broadening
    (offset broadening : ℝ) (hbroadening : 0 < broadening) :
    lorentzianSpectralSecondMoment offset broadening ≤ broadening := by
  unfold lorentzianSpectralSecondMoment lorentzianSpectralKernel
  have hden : 0 < broadening ^ 2 + offset ^ 2 := by positivity
  calc
    offset ^ 2 * (broadening / (broadening ^ 2 + offset ^ 2)) =
        broadening * offset ^ 2 / (broadening ^ 2 + offset ^ 2) := by ring
    _ ≤ broadening := by
      apply (div_le_iff₀ hden).2
      have hcube : 0 ≤ broadening * broadening ^ 2 :=
        mul_nonneg hbroadening.le (sq_nonneg broadening)
      nlinarith

/-- The Lorentzian second-moment density is continuous at fixed nonzero broadening. -/
theorem intervalIntegrable_lorentzianSpectralSecondMoment
    (lower upper broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IntervalIntegrable (fun offset : ℝ =>
      lorentzianSpectralSecondMoment offset broadening)
      volume lower upper := by
  unfold lorentzianSpectralSecondMoment
  exact ((continuous_id.pow 2).mul
    (continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening)).intervalIntegrable
      lower upper

/-- On a symmetric finite window the integrated Lorentzian second moment is bounded by `2 R η`. -/
theorem integral_lorentzianSpectralSecondMoment_symmetric_le
    (radius broadening : ℝ) (hradius : 0 ≤ radius) (hbroadening : 0 < broadening) :
    (∫ offset in -radius..radius,
      lorentzianSpectralSecondMoment offset broadening) ≤
      2 * radius * broadening := by
  have hab : -radius ≤ radius := by linarith
  have hineq :
      ‖∫ offset in -radius..radius,
          lorentzianSpectralSecondMoment offset broadening‖ ≤
        ∫ _offset in -radius..radius, broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with offset
      intro _
      have hnonneg : 0 ≤ lorentzianSpectralSecondMoment offset broadening := by
        unfold lorentzianSpectralSecondMoment
        exact mul_nonneg (sq_nonneg _) (lorentzianSpectralKernel_nonneg _ _ hbroadening.le)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact lorentzianSpectralSecondMoment_le_broadening offset broadening hbroadening
    · exact intervalIntegrable_const
  calc
    (∫ offset in -radius..radius,
      lorentzianSpectralSecondMoment offset broadening) ≤
        |∫ offset in -radius..radius,
          lorentzianSpectralSecondMoment offset broadening| := le_abs_self _
    _ = ‖∫ offset in -radius..radius,
          lorentzianSpectralSecondMoment offset broadening‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ _offset in -radius..radius, broadening := hineq
    _ = 2 * radius * broadening := by simp; ring

/-- Local pole control plus one global compact bound gives a quadratic majorant for the
occupation-weighted spectator error. -/
theorem norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectatorError_le_quadratic
    (band : Band) (e v m px py fermiEnergy offset broadening innerRadius tolerance C : ℝ)
    (hbroadening : 0 ≤ broadening) (hinner : 0 < innerRadius)
    (htolerance : 0 ≤ tolerance) (hC : 0 ≤ C)
    (hlocal : |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance)
    (hglobal : ‖targetCenteredInterbandSpectatorCurrentError
      band e v m px py offset broadening‖ ≤ C) :
    ‖((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentError
            band e v m px py offset broadening)‖ ≤
      tolerance * lorentzianSpectralKernel offset broadening +
        (C / innerRadius ^ 2) *
          lorentzianSpectralSecondMoment offset broadening := by
  have hkernel := lorentzianSpectralKernel_nonneg offset broadening hbroadening
  have hcoeff : 0 ≤ C / innerRadius ^ 2 :=
    div_nonneg hC (sq_nonneg innerRadius)
  have hsecond : 0 ≤ lorentzianSpectralSecondMoment offset broadening := by
    unfold lorentzianSpectralSecondMoment
    exact mul_nonneg (sq_nonneg _) hkernel
  by_cases hnear : |offset| ≤ innerRadius
  · calc
      ‖((zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
          ((lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentError
              band e v m px py offset broadening)‖ ≤
        tolerance * lorentzianSpectralKernel offset broadening :=
          norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectatorError_le
            band e v m px py fermiEnergy offset broadening tolerance hbroadening
              (hlocal hnear)
      _ ≤ tolerance * lorentzianSpectralKernel offset broadening +
          (C / innerRadius ^ 2) *
            lorentzianSpectralSecondMoment offset broadening :=
        le_add_of_nonneg_right (mul_nonneg hcoeff hsecond)
  · have hfar : innerRadius < |offset| := lt_of_not_ge hnear
    have hsq : innerRadius ^ 2 ≤ offset ^ 2 := by
      have h := sq_le_sq₀ hinner.le hfar.le
      simpa [sq_abs] using h
    have hi2 : 0 < innerRadius ^ 2 := sq_pos_of_pos hinner
    have hCscale : C ≤ (C / innerRadius ^ 2) * offset ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hi2).2
      exact mul_le_mul_of_nonneg_left hsq hC
    calc
      ‖((zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
          ((lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentError
              band e v m px py offset broadening)‖ ≤
        C * lorentzianSpectralKernel offset broadening :=
          norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectatorError_le
            band e v m px py fermiEnergy offset broadening C hbroadening hglobal
      _ ≤ ((C / innerRadius ^ 2) * offset ^ 2) *
          lorentzianSpectralKernel offset broadening :=
        mul_le_mul_of_nonneg_right hCscale hkernel
      _ = (C / innerRadius ^ 2) *
          lorentzianSpectralSecondMoment offset broadening := by
        unfold lorentzianSpectralSecondMoment
        ring
      _ ≤ tolerance * lorentzianSpectralKernel offset broadening +
          (C / innerRadius ^ 2) *
            lorentzianSpectralSecondMoment offset broadening :=
        le_add_of_nonneg_left (mul_nonneg htolerance hkernel)

/-- Integrating the quadratic majorant bounds the complete occupation-weighted pole error by a
local Lorentzian mass plus one second-moment term. -/
theorem norm_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral_le
    (band : Band) (e v m px py fermiEnergy innerRadius outerRadius broadening tolerance C : ℝ)
    (hinner : 0 < innerRadius) (houter : 0 ≤ outerRadius)
    (htolerance : 0 ≤ tolerance) (hC : 0 ≤ C) (hbroadening : 0 < broadening)
    (hlocal : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance)
    (hglobal : ∀ offset : ℝ, |offset| ≤ outerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ C) :
    ‖targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
        band e v m px py fermiEnergy outerRadius broadening‖ ≤
      tolerance * (∫ offset in -outerRadius..outerRadius,
        lorentzianSpectralKernel offset broadening) +
        (C / innerRadius ^ 2) *
          (∫ offset in -outerRadius..outerRadius,
            lorentzianSpectralSecondMoment offset broadening) := by
  have hab : -outerRadius ≤ outerRadius := by linarith
  have hkernelInt := intervalIntegrable_lorentzianSpectralKernel
    (-outerRadius) outerRadius broadening hbroadening.ne'
  have hsecondInt := intervalIntegrable_lorentzianSpectralSecondMoment
    (-outerRadius) outerRadius broadening hbroadening.ne'
  unfold targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
  have hineq :
      ‖∫ offset in -outerRadius..outerRadius,
          ((zeroTemperatureOccupation fermiEnergy
              (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
            ((lorentzianSpectralKernel offset broadening : ℂ) *
              targetCenteredInterbandSpectatorCurrentError
                band e v m px py offset broadening)‖ ≤
        ∫ offset in -outerRadius..outerRadius,
          tolerance * lorentzianSpectralKernel offset broadening +
            (C / innerRadius ^ 2) *
              lorentzianSpectralSecondMoment offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with offset
      intro hoffset
      apply norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectatorError_le_quadratic
        band e v m px py fermiEnergy offset broadening innerRadius tolerance C
        hbroadening.le hinner htolerance hC
      · exact hlocal offset
      · apply hglobal offset
        exact abs_le.mpr ⟨le_of_lt hoffset.1, hoffset.2⟩
    · exact (hkernelInt.const_mul tolerance).add
        (hsecondInt.const_mul (C / innerRadius ^ 2))
  rw [intervalIntegral.integral_add
      (hkernelInt.const_mul tolerance)
      (hsecondInt.const_mul (C / innerRadius ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hineq
  exact hineq

/-- A convenient fully scalar bound: the local term is at most `tolerance * π`, while the global
quadratic term is at most `(C / r²) * 2 R η`. -/
theorem norm_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral_le_pi_add_linear
    (band : Band) (e v m px py fermiEnergy innerRadius outerRadius broadening tolerance C : ℝ)
    (hinner : 0 < innerRadius) (houter : 0 ≤ outerRadius)
    (htolerance : 0 ≤ tolerance) (hC : 0 ≤ C) (hbroadening : 0 < broadening)
    (hlocal : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance)
    (hglobal : ∀ offset : ℝ, |offset| ≤ outerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ C) :
    ‖targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
        band e v m px py fermiEnergy outerRadius broadening‖ ≤
      tolerance * Real.pi +
        (C / innerRadius ^ 2) * (2 * outerRadius * broadening) := by
  have hbound := norm_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral_le
    band e v m px py fermiEnergy innerRadius outerRadius broadening tolerance C
    hinner houter htolerance hC hbroadening hlocal hglobal
  have hmass := integral_lorentzianSpectralKernel_symmetric_le_pi outerRadius broadening
  have hsecond := integral_lorentzianSpectralSecondMoment_symmetric_le
    outerRadius broadening houter hbroadening
  have hcoeff : 0 ≤ C / innerRadius ^ 2 :=
    div_nonneg hC (sq_nonneg innerRadius)
  exact hbound.trans <| add_le_add
    (mul_le_mul_of_nonneg_left hmass htolerance)
    (mul_le_mul_of_nonneg_left hsecond hcoeff)

end

end AnomalousHall.MassiveDirac
