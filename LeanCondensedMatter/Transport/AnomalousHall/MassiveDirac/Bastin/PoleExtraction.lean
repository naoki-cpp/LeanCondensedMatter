import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorLimit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Regular-factor extraction at a massive-Dirac Bastin pole

The fixed-window spectator error vanishes in the positive zero-broadening limit.  This file now
returns to the physical regular factor itself.  Its Lorentzian-weighted target-centered integral is
split exactly into the already-controlled error integral plus the scalar Lorentzian mass multiplying
the regular factor evaluated at the target pole.

The subsequent limit therefore reduces to the existing Lorentzian mass theorem and the fixed-window
error theorem.  No momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory

/-- Lorentzian-weighted target-centered integral of the regular interband spectator/current factor.
-/
noncomputable def targetCenteredInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    (lorentzianSpectralKernel offset broadening : ℂ) *
      targetCenteredInterbandSpectatorCurrentFactor
        band e v m px py (offset, broadening)

private theorem real_smul_complex_eq_mul (r : ℝ) (z : ℂ) :
    r • z = (r : ℂ) * z := by
  rfl

/-- At fixed nonzero broadening, the regular-factor pole integral is exactly its spectator-error
integral plus the scalar Lorentzian mass multiplying the target-pole value. -/
theorem targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_error_add_mass_smul_pole
    (band : Band) (e v m px py radius broadening : ℝ)
    (hradiusNonneg : 0 ≤ radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandSpectatorCurrentPoleIntegral
        band e v m px py radius broadening =
      targetCenteredInterbandSpectatorCurrentErrorIntegral
          band e v m px py radius broadening +
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0) := by
  have herrorInt :=
    intervalIntegrable_targetCenteredInterbandSpectatorCurrentErrorIntegrand
      band e v m px py radius broadening hradiusNonneg hradius hbroadening
  have hkernelCont :=
    continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening
  have hpoleInt : IntervalIntegrable
      (fun offset : ℝ =>
        lorentzianSpectralKernel offset broadening •
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
      MeasureTheory.volume (-radius) radius := by
    exact (hkernelCont.smul continuous_const).intervalIntegrable
      (μ := MeasureTheory.volume) (-radius) radius
  unfold targetCenteredInterbandSpectatorCurrentPoleIntegral
  calc
    (∫ offset in -radius..radius,
        (lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (offset, broadening)) =
      ∫ offset in -radius..radius,
        targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset +
          lorentzianSpectralKernel offset broadening •
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (0, 0) := by
        apply intervalIntegral.integral_congr
        intro offset _
        unfold targetCenteredInterbandSpectatorCurrentErrorIntegrand
          targetCenteredInterbandSpectatorCurrentError
        change
          (lorentzianSpectralKernel offset broadening : ℂ) *
              targetCenteredInterbandSpectatorCurrentFactor
                band e v m px py (offset, broadening) =
            (lorentzianSpectralKernel offset broadening : ℂ) *
                (targetCenteredInterbandSpectatorCurrentFactor
                    band e v m px py (offset, broadening) -
                  targetCenteredInterbandSpectatorCurrentFactor
                    band e v m px py (0, 0)) +
              lorentzianSpectralKernel offset broadening •
                targetCenteredInterbandSpectatorCurrentFactor
                  band e v m px py (0, 0)
        rw [real_smul_complex_eq_mul]
        ring
    _ = (∫ offset in -radius..radius,
          targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset) +
        ∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening •
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (0, 0) := by
        exact intervalIntegral.integral_add herrorInt hpoleInt
    _ = targetCenteredInterbandSpectatorCurrentErrorIntegral
          band e v m px py radius broadening +
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0) := by
        unfold targetCenteredInterbandSpectatorCurrentErrorIntegral
        rw [intervalIntegral.integral_smul_const]

end

end AnomalousHall.MassiveDirac
