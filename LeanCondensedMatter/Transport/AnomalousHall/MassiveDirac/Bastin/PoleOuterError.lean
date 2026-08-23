import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleInnerError
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Outer-window Lorentzian error bound at a massive-Dirac Bastin pole

The inner pole window is controlled by local continuity.  On the complementary annulus inside a
fixed target-centered window, the spectator/current error only needs a uniform compact bound,
because the Lorentzian mass of that annulus vanishes with the broadening.

This file identifies the sum of the two scalar outer-interval masses with the existing Lorentzian
tail mass and bounds the corresponding complex spectator-error integral by a compact constant times
that tail mass.  No momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory

/-- Lorentzian mass in the two outer intervals between an inner and outer symmetric radius. -/
def lorentzianSpectralOuterMass (innerRadius outerRadius broadening : ℝ) : ℝ :=
  (∫ offset in -outerRadius..-innerRadius,
      lorentzianSpectralKernel offset broadening) +
    ∫ offset in innerRadius..outerRadius,
      lorentzianSpectralKernel offset broadening

/-- At nonzero broadening, the two explicit outer intervals carry exactly the previously defined
Lorentzian tail mass. -/
theorem lorentzianSpectralOuterMass_eq_tailMass
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
  unfold lorentzianSpectralOuterMass QuantumTheory.Transport.lorentzianSpectralTailMass
  linarith

/-- The Lorentzian-weighted spectator error integrated over both outer intervals. -/
noncomputable def targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
    (band : Band) (e v m px py innerRadius outerRadius broadening : ℝ) : ℂ :=
  (∫ offset in -outerRadius..-innerRadius,
      (lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentError
          band e v m px py offset broadening) +
    ∫ offset in innerRadius..outerRadius,
      (lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentError
          band e v m px py offset broadening

/-- A uniform spectator-error bound on a symmetric annulus bounds the two outer integrals by that
constant times the Lorentzian tail mass. -/
theorem norm_targetCenteredInterbandSpectatorCurrentOuterErrorIntegral_le
    (band : Band) (e v m px py innerRadius outerRadius broadening C : ℝ)
    (hinner : 0 ≤ innerRadius) (hnested : innerRadius ≤ outerRadius)
    (hbroadening : 0 < broadening)
    (herror : ∀ offset : ℝ, innerRadius ≤ |offset| → |offset| ≤ outerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ C) :
    ‖targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
        band e v m px py innerRadius outerRadius broadening‖ ≤
      C * lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  have hleftOrder : -outerRadius ≤ -innerRadius := by linarith
  have hrightOrder : innerRadius ≤ outerRadius := hnested
  have hleftKernel := intervalIntegrable_lorentzianSpectralKernel
    (-outerRadius) (-innerRadius) broadening hbroadening.ne'
  have hrightKernel := intervalIntegrable_lorentzianSpectralKernel
    innerRadius outerRadius broadening hbroadening.ne'
  have hleftBound :
      ‖∫ offset in -outerRadius..-innerRadius,
          (lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentError
              band e v m px py offset broadening‖ ≤
        ∫ offset in -outerRadius..-innerRadius,
          C * lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hleftOrder
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
        band e v m px py offset broadening C hbroadening.le
      have hoffsetNonpos : offset ≤ 0 := by linarith [hoffset.2]
      apply herror offset
      · rw [abs_of_nonpos hoffsetNonpos]
        linarith [hoffset.2]
      · rw [abs_of_nonpos hoffsetNonpos]
        linarith [hoffset.1]
    · exact hleftKernel.const_mul C
  have hrightBound :
      ‖∫ offset in innerRadius..outerRadius,
          (lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentError
              band e v m px py offset broadening‖ ≤
        ∫ offset in innerRadius..outerRadius,
          C * lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hrightOrder
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
        band e v m px py offset broadening C hbroadening.le
      have hoffsetNonneg : 0 ≤ offset := by linarith [hoffset.1]
      apply herror offset
      · rw [abs_of_nonneg hoffsetNonneg]
        linarith [hoffset.1]
      · rw [abs_of_nonneg hoffsetNonneg]
        exact hoffset.2
    · exact hrightKernel.const_mul C
  calc
    ‖targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
        band e v m px py innerRadius outerRadius broadening‖ ≤
        ‖∫ offset in -outerRadius..-innerRadius,
            (lorentzianSpectralKernel offset broadening : ℂ) *
              targetCenteredInterbandSpectatorCurrentError
                band e v m px py offset broadening‖ +
          ‖∫ offset in innerRadius..outerRadius,
            (lorentzianSpectralKernel offset broadening : ℂ) *
              targetCenteredInterbandSpectatorCurrentError
                band e v m px py offset broadening‖ := by
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

/-- The compact target-window bound supplies the annular hypothesis required by the outer-error
estimate whenever the broadening lies in the chosen compact range. -/
theorem exists_nonneg_bound_targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
    (band : Band) (e v m px py innerRadius outerRadius broadening broadeningMax : ℝ)
    (hinner : 0 ≤ innerRadius) (hnested : innerRadius ≤ outerRadius)
    (houter : outerRadius < |interbandEnergyGap band v m px py|)
    (hbroadening : 0 < broadening) (hbroadeningMax : broadening ≤ broadeningMax) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
          band e v m px py innerRadius outerRadius broadening‖ ≤
        C * lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  rcases exists_nonneg_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_le_on_rectangle
      band e v m px py outerRadius broadeningMax houter with ⟨C, hCnonneg, hC⟩
  refine ⟨C, hCnonneg, ?_⟩
  apply norm_targetCenteredInterbandSpectatorCurrentOuterErrorIntegral_le
    band e v m px py innerRadius outerRadius broadening C hinner hnested hbroadening
  intro offset _ hOffsetOuter
  apply hC (offset, broadening)
  refine ⟨?_, ⟨hbroadening.le, hbroadeningMax⟩⟩
  exact abs_le.mp hOffsetOuter

end

end AnomalousHall.MassiveDirac
