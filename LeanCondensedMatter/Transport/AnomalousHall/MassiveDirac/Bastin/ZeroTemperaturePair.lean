import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialEnergyBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialPairUniformBound
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureOccupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature occupation-weighted interband Bastin pair

The finite-radial dominated-convergence chain built so far concerns the target-centered interband
pair before the physical occupation factor is applied.  This file starts the final occupation
bridge by inserting the zero-temperature Fermi weight directly in that finite-broadening pair.

Because the occupation takes only the values `0` and `1`, it does not enlarge the uniform radial
bound already proved for the unweighted pair.  This gives the domination input needed for the later
occupation-weighted momentum DCT while keeping the exact Fermi-edge limit separate.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport

/-- Target-centered regular pole integral with the physical zero-temperature occupation inserted. -/
noncomputable def targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py fermiEnergy radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    ((zeroTemperatureOccupation fermiEnergy
        (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
      ((lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentFactor
          band e v m px py (offset, broadening))

/-- Target-centered interband Bastin pair with the physical zero-temperature occupation inserted
before the energy integration. -/
noncomputable def targetCenteredZeroTemperatureInterbandBastinPairIntegral
    (band : Band) (e v m px py fermiEnergy radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    ((zeroTemperatureOccupation fermiEnergy
        (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
      bastinBandPairContribution (oppositeBand band) band e v m px py
        (bandEnergy band v m px py + offset) broadening

/-- For nonzero broadening, occupation weighting preserves the exact `-2 i` pole factorization. -/
theorem targetCenteredZeroTemperatureInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    (band : Band) (e v m px py fermiEnergy radius broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    targetCenteredZeroTemperatureInterbandBastinPairIntegral
        band e v m px py fermiEnergy radius broadening =
      (-2 * Complex.I) *
        targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
          band e v m px py fermiEnergy radius broadening := by
  unfold targetCenteredZeroTemperatureInterbandBastinPairIntegral
    targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro offset _
  change
    ((zeroTemperatureOccupation fermiEnergy
        (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
        bastinBandPairContribution (oppositeBand band) band e v m px py
          (bandEnergy band v m px py + offset) broadening =
      (-2 * Complex.I) *
        (((zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
          ((lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (offset, broadening)))
  rw [bastinBandPairContribution_opposite_source_eq_lorentzian
    band e v m px py (bandEnergy band v m px py + offset) broadening hbroadening]
  unfold targetCenteredInterbandSpectatorCurrentFactor
  rw [show bandEnergy band v m px py + offset - bandEnergy band v m px py = offset by ring]
  ring

/-- Inserting zero-temperature occupation does not enlarge the pointwise Lorentzian/spectator
bound on the radial axis. -/
theorem norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectator_radial_le
    (band : Band) (e v m p fermiEnergy offset radius broadening : ℝ)
    (hm : m ≠ 0) (hradius : radius < 2 * |m|) (hoffset : |offset| ≤ radius)
    (hbroadening : 0 ≤ broadening) :
    ‖((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m p 0 + offset) : ℝ) : ℂ) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m p 0 (offset, broadening))‖ ≤
      radialInterbandSpectatorUniformBound e v m radius *
        lorentzianSpectralKernel offset broadening := by
  rw [norm_mul]
  calc
    ‖((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m p 0 + offset) : ℝ) : ℂ)‖ *
        ‖(lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m p 0 (offset, broadening)‖ ≤
      1 * ‖(lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m p 0 (offset, broadening)‖ := by
        exact mul_le_mul_of_nonneg_right
          (QuantumTheory.Transport.norm_zeroTemperatureOccupation_complex_le_one
            fermiEnergy (bandEnergy band v m p 0 + offset)) (norm_nonneg _)
    _ = ‖(lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m p 0 (offset, broadening)‖ := by ring
    _ ≤ radialInterbandSpectatorUniformBound e v m radius *
        lorentzianSpectralKernel offset broadening :=
      norm_lorentzian_mul_targetCenteredInterbandSpectatorCurrentFactor_radial_le
        band e v m p offset radius broadening hm hradius hoffset hbroadening

/-- The occupation-weighted regular pole integral inherits exactly the same uniform Lorentzian-mass
bound as the unweighted one. -/
theorem norm_targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral_radial_le
    (band : Band) (e v m p fermiEnergy radius broadening : ℝ)
    (hm : m ≠ 0) (hradiusPos : 0 < radius) (hradius : radius < 2 * |m|)
    (hbroadening : 0 < broadening) :
    ‖targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
        band e v m p 0 fermiEnergy radius broadening‖ ≤
      radialInterbandSpectatorUniformBound e v m radius *
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) := by
  have hab : -radius ≤ radius := by linarith
  have hkernelInt := QuantumTheory.Transport.intervalIntegrable_lorentzianSpectralKernel
    (-radius) radius broadening hbroadening.ne'
  unfold targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
  have hineq :
      ‖∫ offset in -radius..radius,
          ((zeroTemperatureOccupation fermiEnergy
              (bandEnergy band v m p 0 + offset) : ℝ) : ℂ) *
            ((lorentzianSpectralKernel offset broadening : ℂ) *
              targetCenteredInterbandSpectatorCurrentFactor
                band e v m p 0 (offset, broadening))‖ ≤
        ∫ offset in -radius..radius,
          radialInterbandSpectatorUniformBound e v m radius *
            lorentzianSpectralKernel offset broadening := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with offset
      intro hoffset
      apply norm_zeroTemperatureOccupation_mul_lorentzian_mul_spectator_radial_le
        band e v m p fermiEnergy offset radius broadening hm hradius
      · exact abs_le.mpr ⟨le_of_lt hoffset.1, hoffset.2⟩
      · exact hbroadening.le
    · exact hkernelInt.const_mul (radialInterbandSpectatorUniformBound e v m radius)
  rw [intervalIntegral.integral_const_mul] at hineq
  exact hineq

/-- The complete occupation-weighted target-centered pair is uniformly bounded in radial momentum
and positive broadening by the same constant as the unweighted pair. -/
theorem norm_targetCenteredZeroTemperatureInterbandBastinPairIntegral_radial_le
    (band : Band) (e v m p fermiEnergy radius broadening : ℝ)
    (hm : m ≠ 0) (hradiusPos : 0 < radius) (hradius : radius < 2 * |m|)
    (hbroadening : 0 < broadening) :
    ‖targetCenteredZeroTemperatureInterbandBastinPairIntegral
        band e v m p 0 fermiEnergy radius broadening‖ ≤
      2 * (radialInterbandSpectatorUniformBound e v m radius * Real.pi) := by
  rw [targetCenteredZeroTemperatureInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    band e v m p 0 fermiEnergy radius broadening hbroadening.ne']
  have hpole :=
    norm_targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral_radial_le
      band e v m p fermiEnergy radius broadening hm hradiusPos hradius hbroadening
  have hmass := QuantumTheory.Transport.integral_lorentzianSpectralKernel_symmetric_le_pi
    radius broadening
  have hC := radialInterbandSpectatorUniformBound_nonneg e v m radius
  have hpolePi :
      ‖targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
          band e v m p 0 fermiEnergy radius broadening‖ ≤
        radialInterbandSpectatorUniformBound e v m radius * Real.pi :=
    hpole.trans (mul_le_mul_of_nonneg_left hmass hC)
  have hfactor : ‖(-2 * Complex.I : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, hfactor]
  exact mul_le_mul_of_nonneg_left hpolePi (by norm_num)

end

end AnomalousHall.MassiveDirac
