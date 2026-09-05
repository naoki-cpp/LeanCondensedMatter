import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialSpectatorUniformBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Uniform bound for the finite-broadening radial Bastin pair

The uniform radial spectator bound can be integrated without losing the Lorentzian pole mass.
For positive broadening the Lorentzian is nonnegative, so the interval-integral norm is controlled
by the spectator constant times the exact symmetric Lorentzian mass.  Since that mass is at most
`π`, the full interband Bastin pair receives a momentum- and broadening-independent bound.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory

/-- The Lorentzian-weighted radial spectator integrand inherits the uniform spectator bound. -/
theorem norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentFactor_radial_le
    (band : Band) (e v m p offset radius broadening : ℝ)
    (hm : m ≠ 0) (hradius : radius < 2 * |m|) (hoffset : |offset| ≤ radius)
    (hbroadening : 0 ≤ broadening) :
    ‖(lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentFactor
          band e v m p 0 (offset, broadening)‖ ≤
      radialInterbandSpectatorUniformBound e v m radius *
        lorentzianSpectralKernel offset broadening := by
  have hkernel := QuantumTheory.Transport.lorentzianSpectralKernel_nonneg
    offset broadening hbroadening
  have hnorm :
      ‖(lorentzianSpectralKernel offset broadening : ℂ)‖ =
        lorentzianSpectralKernel offset broadening := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkernel]
  rw [norm_mul, hnorm]
  calc
    lorentzianSpectralKernel offset broadening *
        ‖targetCenteredInterbandSpectatorCurrentFactor
          band e v m p 0 (offset, broadening)‖ ≤
      lorentzianSpectralKernel offset broadening *
        radialInterbandSpectatorUniformBound e v m radius :=
      mul_le_mul_of_nonneg_left
        (norm_targetCenteredInterbandSpectatorCurrentFactor_radial_le
          band e v m p offset radius broadening hm hradius hoffset) hkernel
    _ = radialInterbandSpectatorUniformBound e v m radius *
        lorentzianSpectralKernel offset broadening := by ring

/-- Integrating over the fixed target window preserves the Lorentzian mass exactly in the upper
bound. -/
theorem norm_targetCenteredInterbandSpectatorCurrentPoleIntegral_radial_le
    (band : Band) (e v m p radius broadening : ℝ)
    (hm : m ≠ 0) (hradiusPos : 0 < radius) (hradius : radius < 2 * |m|)
    (hbroadening : 0 < broadening) :
    ‖targetCenteredInterbandSpectatorCurrentPoleIntegral
        band e v m p 0 radius broadening‖ ≤
      radialInterbandSpectatorUniformBound e v m radius *
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) := by
  have hab : -radius ≤ radius := by linarith
  have hkernelInt := QuantumTheory.Transport.intervalIntegrable_lorentzianSpectralKernel
    (-radius) radius broadening hbroadening.ne'
  unfold targetCenteredInterbandSpectatorCurrentPoleIntegral
    QuantumTheory.Transport.lorentzianRegularFactorIntegral
  have hineq :
      ‖∫ offset in -radius..radius,
          (lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m p 0 (offset, broadening)‖ ≤
        ∫ offset in -radius..radius,
          radialInterbandSpectatorUniformBound e v m radius *
            lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with offset
      intro hoffset
      apply norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentFactor_radial_le
        band e v m p offset radius broadening hm hradius
      · exact abs_le.mpr ⟨le_of_lt hoffset.1, hoffset.2⟩
      · exact hbroadening.le
    · exact hkernelInt.const_mul (radialInterbandSpectatorUniformBound e v m radius)
  rw [intervalIntegral.integral_const_mul] at hineq
  exact hineq

/-- The explicit spectator bound is nonnegative. -/
theorem radialInterbandSpectatorUniformBound_nonneg
    (e v m radius : ℝ) :
    0 ≤ radialInterbandSpectatorUniformBound e v m radius := by
  unfold radialInterbandSpectatorUniformBound
  positivity

/-- Uniform norm bound for the complete target-centered interband Bastin pair on the radial axis. -/
theorem norm_targetCenteredInterbandBastinPairIntegral_radial_le
    (band : Band) (e v m p radius broadening : ℝ)
    (hm : m ≠ 0) (hradiusPos : 0 < radius) (hradius : radius < 2 * |m|)
    (hbroadening : 0 < broadening) :
    ‖targetCenteredInterbandBastinPairIntegral
        band e v m p 0 radius broadening‖ ≤
      2 * (radialInterbandSpectatorUniformBound e v m radius * Real.pi) := by
  rw [targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    band e v m p 0 radius broadening hbroadening.ne']
  have hpole :=
    norm_targetCenteredInterbandSpectatorCurrentPoleIntegral_radial_le
      band e v m p radius broadening hm hradiusPos hradius hbroadening
  have hmass := QuantumTheory.Transport.integral_lorentzianSpectralKernel_symmetric_le_pi
    radius broadening
  have hC := radialInterbandSpectatorUniformBound_nonneg e v m radius
  have hpolePi :
      ‖targetCenteredInterbandSpectatorCurrentPoleIntegral
          band e v m p 0 radius broadening‖ ≤
        radialInterbandSpectatorUniformBound e v m radius * Real.pi :=
    hpole.trans (mul_le_mul_of_nonneg_left hmass hC)
  have hfactor : ‖(-2 * Complex.I : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, hfactor]
  exact mul_le_mul_of_nonneg_left hpolePi (by norm_num)

end

end AnomalousHall.MassiveDirac
