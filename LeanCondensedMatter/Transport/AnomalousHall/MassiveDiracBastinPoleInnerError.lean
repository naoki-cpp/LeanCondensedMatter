import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Inner-window Lorentzian error bound at a massive-Dirac Bastin pole

On a sufficiently small target-centered window, the regular spectator/current factor is uniformly
close to its pole value.  Because the positive-broadening Lorentzian kernel is nonnegative, this
pointwise error estimate passes directly through the interval integral with the Lorentzian mass as
the scalar prefactor.

This is the inner-window half of the pole-error limit.  The complementary outer annulus is handled
separately using the compact bound and the vanishing Lorentzian tail mass.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory

/-- The regular spectator/current error relative to its target-pole value. -/
noncomputable def targetCenteredInterbandSpectatorCurrentError
    (band : Band) (e v m px py offset broadening : ℝ) : ℂ :=
  targetCenteredInterbandSpectatorCurrentFactor band e v m px py (offset, broadening) -
    targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0)

/-- A pointwise norm bound on the spectator error is preserved after multiplication by the
nonnegative Lorentzian kernel. -/
theorem norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
    (band : Band) (e v m px py offset broadening tolerance : ℝ)
    (hbroadening : 0 ≤ broadening)
    (herror : ‖targetCenteredInterbandSpectatorCurrentError
      band e v m px py offset broadening‖ ≤ tolerance) :
    ‖(lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentError
          band e v m px py offset broadening‖ ≤
      tolerance * lorentzianSpectralKernel offset broadening := by
  have hkernel := lorentzianSpectralKernel_nonneg offset broadening hbroadening
  have hnorm :
      ‖(lorentzianSpectralKernel offset broadening : ℂ)‖ =
        lorentzianSpectralKernel offset broadening := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hkernel.abs_eq
  rw [norm_mul, hnorm]
  calc
    lorentzianSpectralKernel offset broadening *
        ‖targetCenteredInterbandSpectatorCurrentError
          band e v m px py offset broadening‖ ≤
      lorentzianSpectralKernel offset broadening * tolerance :=
        mul_le_mul_of_nonneg_left herror hkernel
    _ = tolerance * lorentzianSpectralKernel offset broadening := by ring

/-- If the spectator error is bounded by `tolerance` on a symmetric inner window, then the norm of
its Lorentzian-weighted integral is bounded by `tolerance` times the Lorentzian mass of that window.
-/
theorem norm_integral_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
    (band : Band) (e v m px py innerRadius broadening tolerance : ℝ)
    (hinner : 0 ≤ innerRadius) (hbroadening : 0 < broadening)
    (herror : ∀ offset : ℝ, |offset| ≤ innerRadius →
      ‖targetCenteredInterbandSpectatorCurrentError
        band e v m px py offset broadening‖ ≤ tolerance) :
    ‖∫ offset in -innerRadius..innerRadius,
        (lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentError
            band e v m px py offset broadening‖ ≤
      tolerance *
        (∫ offset in -innerRadius..innerRadius,
          lorentzianSpectralKernel offset broadening) := by
  have hab : -innerRadius ≤ innerRadius := by linarith
  have hkernelInt := intervalIntegrable_lorentzianSpectralKernel
    (-innerRadius) innerRadius broadening hbroadening.ne'
  have hineq :
      ‖∫ offset in -innerRadius..innerRadius,
          (lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentError
              band e v m px py offset broadening‖ ≤
        ∫ offset in -innerRadius..innerRadius,
          tolerance * lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentError_le
        band e v m px py offset broadening tolerance hbroadening.le
      apply herror offset
      exact abs_le.mpr ⟨le_of_lt hoffset.1, hoffset.2⟩
    · exact hkernelInt.const_mul tolerance
  rw [intervalIntegral.integral_const_mul] at hineq
  exact hineq

end

end AnomalousHall.MassiveDirac
