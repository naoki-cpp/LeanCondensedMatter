import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorSplit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Combined fixed-window error bound at a massive-Dirac Bastin pole

The full target-centered spectator-error integral has already been split exactly into an inner pole
window and an outer annulus.  The inner part is controlled by local continuity times the Lorentzian
mass, while the outer part is controlled by a uniform compact bound times the Lorentzian tail mass.

This file combines those two estimates into the deterministic inequality used by the subsequent
zero-broadening limit.  No limit or momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Combining the inner local estimate and outer annular estimate bounds the full fixed-window
spectator error by the sum of the corresponding Lorentzian masses. -/
theorem norm_targetCenteredInterbandSpectatorCurrentErrorIntegral_le_inner_add_tail
    (band : Band) (e v m px py innerRadius outerRadius broadening tolerance C : ℝ)
    (hinner : 0 ≤ innerRadius) (hnested : innerRadius ≤ outerRadius)
    (houter : outerRadius < |interbandEnergyGap band v m px py|)
    (hbroadening : 0 < broadening)
    (hlocal : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance)
    (hannulus : ∀ offset : ℝ, innerRadius ≤ |offset| → |offset| ≤ outerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ C) :
    ‖targetCenteredInterbandSpectatorCurrentErrorIntegral
        band e v m px py outerRadius broadening‖ ≤
      tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) +
        C * lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  rw [targetCenteredInterbandSpectatorCurrentErrorIntegral_eq_outer_add_inner
    band e v m px py innerRadius outerRadius broadening hinner hnested houter
    hbroadening.ne']
  calc
    ‖targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
          band e v m px py innerRadius outerRadius broadening +
        (∫ offset in -innerRadius..innerRadius,
          targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset)‖ ≤
      ‖targetCenteredInterbandSpectatorCurrentOuterErrorIntegral
          band e v m px py innerRadius outerRadius broadening‖ +
        ‖∫ offset in -innerRadius..innerRadius,
          targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset‖ :=
      norm_add_le _ _
    _ ≤ C * lorentzianSpectralTailMass innerRadius outerRadius broadening +
        tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) := by
      apply add_le_add
      · exact norm_targetCenteredInterbandSpectatorCurrentOuterErrorIntegral_le
          band e v m px py innerRadius outerRadius broadening C
          hinner hnested hbroadening hannulus
      · simpa [targetCenteredInterbandSpectatorCurrentErrorIntegrand] using
          norm_integral_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
            band e v m px py innerRadius broadening tolerance
            hinner hbroadening hlocal
    _ = tolerance *
          (∫ offset in -innerRadius..innerRadius,
            lorentzianSpectralKernel offset broadening) +
        C * lorentzianSpectralTailMass innerRadius outerRadius broadening := by
      ring

end

end AnomalousHall.MassiveDirac
