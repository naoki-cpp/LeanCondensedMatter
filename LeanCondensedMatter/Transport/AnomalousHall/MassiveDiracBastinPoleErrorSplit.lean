import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleOuterError
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Splitting the massive-Dirac Bastin pole error into inner and outer windows

The local and tail estimates are proved on separate energy regions.  This file supplies the exact
analytic glue: at fixed nonzero broadening the Lorentzian-weighted spectator error is continuous
and interval integrable on every target-centered window separated from the opposite band, and the
full symmetric-window integral splits into the two outer intervals plus the inner pole interval.

No zero-broadening limit or momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory

/-- Lorentzian-weighted regular spectator error at fixed target-centered offset. -/
noncomputable def targetCenteredInterbandSpectatorCurrentErrorIntegrand
    (band : Band) (e v m px py broadening offset : ℝ) : ℂ :=
  (lorentzianSpectralKernel offset broadening : ℂ) *
    targetCenteredInterbandSpectatorCurrentError band e v m px py offset broadening

/-- At fixed broadening, the regular spectator error is continuous throughout a target-centered
energy window narrower than the interband gap. -/
theorem continuousOn_targetCenteredInterbandSpectatorCurrentError_fixedBroadening
    (band : Band) (e v m px py radius broadening : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    ContinuousOn
      (fun offset : ℝ =>
        targetCenteredInterbandSpectatorCurrentError band e v m px py offset broadening)
      (Set.Icc (-radius) radius) := by
  intro offset hoffset
  have hfactor :=
    continuousAt_targetCenteredInterbandSpectatorCurrentFactor_on_targetWindow
      band e v m px py radius (offset, broadening) hradius (abs_le.mpr hoffset)
  have hpair : ContinuousAt (fun x : ℝ => (x, broadening)) offset := by
    fun_prop
  have hcomp : ContinuousAt
      (fun x : ℝ =>
        targetCenteredInterbandSpectatorCurrentFactor band e v m px py (x, broadening))
      offset := by
    change Filter.Tendsto
      (fun x : ℝ =>
        targetCenteredInterbandSpectatorCurrentFactor band e v m px py (x, broadening))
      (nhds offset)
      (nhds
        (targetCenteredInterbandSpectatorCurrentFactor band e v m px py (offset, broadening)))
    exact Filter.Tendsto.comp hfactor hpair
  have hconst : ContinuousAt
      (fun _ : ℝ => targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
      offset := continuousAt_const
  simpa [targetCenteredInterbandSpectatorCurrentError] using
    (hcomp.sub hconst).continuousWithinAt

/-- At fixed nonzero broadening, the complete Lorentzian-weighted spectator error is continuous on
any target-centered window narrower than the interband gap. -/
theorem continuousOn_targetCenteredInterbandSpectatorCurrentErrorIntegrand_fixedBroadening
    (band : Band) (e v m px py radius broadening : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hbroadening : broadening ≠ 0) :
    ContinuousOn
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      (Set.Icc (-radius) radius) := by
  have hkernelReal :=
    continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening
  have hkernelComplex : Continuous
      (fun offset : ℝ => (lorentzianSpectralKernel offset broadening : ℂ)) :=
    Complex.continuous_ofReal.comp hkernelReal
  have herror :=
    continuousOn_targetCenteredInterbandSpectatorCurrentError_fixedBroadening
      band e v m px py radius broadening hradius
  unfold targetCenteredInterbandSpectatorCurrentErrorIntegrand
  exact hkernelComplex.continuousOn.mul herror

/-- The Lorentzian-weighted spectator error is interval integrable on a positive symmetric target
window separated from the opposite band. -/
theorem intervalIntegrable_targetCenteredInterbandSpectatorCurrentErrorIntegrand
    (band : Band) (e v m px py radius broadening : ℝ)
    (hradiusNonneg : 0 ≤ radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hbroadening : broadening ≠ 0) :
    IntervalIntegrable
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      MeasureTheory.volume (-radius) radius := by
  have hab : -radius ≤ radius := by linarith
  exact
    (continuousOn_targetCenteredInterbandSpectatorCurrentErrorIntegrand_fixedBroadening
      band e v m px py radius broadening hradius hbroadening).intervalIntegrable_of_Icc hab

/-- Full symmetric-window Lorentzian-weighted spectator error. -/
noncomputable def targetCenteredInterbandSpectatorCurrentErrorIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    targetCenteredInterbandSpectatorCurrentErrorIntegrand
      band e v m px py broadening offset

/-- The full fixed-window error is exactly the outer-annulus error plus the inner-pole error. -/
theorem targetCenteredInterbandSpectatorCurrentErrorIntegral_eq_outer_add_inner
    (band : Band) (e v m px py innerRadius outerRadius broadening : ℝ)
    (hinner : 0 ≤ innerRadius) (hnested : innerRadius ≤ outerRadius)
    (houter : outerRadius < |interbandEnergyGap band v m px py|)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandSpectatorCurrentErrorIntegral
        band e v m px py outerRadius broadening =
      targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
          band e v m px py innerRadius outerRadius broadening +
        (∫ offset in -innerRadius..innerRadius,
          targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset) := by
  have houterNonneg : 0 ≤ outerRadius := le_trans hinner hnested
  have hcont :=
    continuousOn_targetCenteredInterbandSpectatorCurrentErrorIntegrand_fixedBroadening
      band e v m px py outerRadius broadening houter hbroadening
  have hleftCont : ContinuousOn
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      (Set.Icc (-outerRadius) (-innerRadius)) := by
    apply hcont.mono
    intro offset hoffset
    constructor
    · exact hoffset.1
    · linarith [hoffset.2]
  have hmiddleCont : ContinuousOn
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      (Set.Icc (-innerRadius) innerRadius) := by
    apply hcont.mono
    intro offset hoffset
    constructor <;> linarith [hoffset.1, hoffset.2]
  have hrightCont : ContinuousOn
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      (Set.Icc innerRadius outerRadius) := by
    apply hcont.mono
    intro offset hoffset
    constructor
    · linarith [hoffset.1]
    · exact hoffset.2
  have hleft : IntervalIntegrable
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      MeasureTheory.volume (-outerRadius) (-innerRadius) := by
    exact hleftCont.intervalIntegrable_of_Icc (by linarith)
  have hmiddle : IntervalIntegrable
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      MeasureTheory.volume (-innerRadius) innerRadius := by
    exact hmiddleCont.intervalIntegrable_of_Icc (by linarith)
  have hright : IntervalIntegrable
      (targetCenteredInterbandSpectatorCurrentErrorIntegrand band e v m px py broadening)
      MeasureTheory.volume innerRadius outerRadius := by
    exact hrightCont.intervalIntegrable_of_Icc hnested
  have hleftMiddle := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hwhole := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  unfold targetCenteredInterbandSpectatorCurrentErrorIntegral
  rw [← hwhole, ← hleftMiddle]
  unfold targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
  unfold targetCenteredInterbandSpectatorCurrentErrorIntegrand
  ring

end

end AnomalousHall.MassiveDirac
