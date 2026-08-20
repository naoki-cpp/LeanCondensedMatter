import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePoleErrorLimit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Regular-factor extraction for the zero-temperature occupation-weighted Bastin pole

The zero-temperature target-centered pole has two ingredients with independently controlled limits:
its scalar Lorentzian occupation weight tends to `π`, `0`, or `π/2`, and its occupation-weighted
regular-spectator error tends to zero.  This file proves the exact finite-broadening decomposition
that joins those two statements and then extracts the complete weighted interband Bastin-pair limit.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory

/-- The target-centered zero-temperature occupation is measurable in the offset variable. -/
theorem measurable_targetCenteredZeroTemperatureOccupation
    (center fermiEnergy : ℝ) :
    Measurable (fun offset : ℝ =>
      zeroTemperatureOccupation fermiEnergy (center + offset)) := by
  unfold zeroTemperatureOccupation
  exact Measurable.ite
    (measurableSet_lt (measurable_const.add measurable_id) measurable_const)
    measurable_const measurable_const

/-- The target-centered zero-temperature Lorentzian scalar integrand is interval integrable for
nonzero broadening. -/
theorem intervalIntegrable_targetCenteredZeroTemperatureLorentzianIntegrand
    (center fermiEnergy lower upper broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IntervalIntegrable
      (fun offset : ℝ =>
        zeroTemperatureOccupation fermiEnergy (center + offset) *
          lorentzianSpectralKernel offset broadening)
      volume lower upper := by
  have hkernel := intervalIntegrable_lorentzianSpectralKernel
    lower upper broadening hbroadening
  apply hkernel.mono_fun
  · exact ((measurable_targetCenteredZeroTemperatureOccupation center fermiEnergy).mul
      (continuous_lorentzianSpectralKernel_fixed_broadening
        broadening hbroadening).measurable).aestronglyMeasurable
  · filter_upwards with offset
    have hoccReal : |zeroTemperatureOccupation fermiEnergy (center + offset)| ≤ 1 := by
      by_cases h : center + offset < fermiEnergy <;>
        simp [zeroTemperatureOccupation, h]
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc
      |zeroTemperatureOccupation fermiEnergy (center + offset)| *
          |lorentzianSpectralKernel offset broadening| ≤
        1 * |lorentzianSpectralKernel offset broadening| :=
          mul_le_mul_of_nonneg_right hoccReal (abs_nonneg _)
      _ = |lorentzianSpectralKernel offset broadening| := one_mul _

/-- Multiplying the existing regular-spectator error integrand by zero-temperature occupation
preserves interval integrability on the fixed target window. -/
theorem intervalIntegrable_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegrand
    (band : Band) (e v m px py fermiEnergy radius broadening : ℝ)
    (hradiusNonneg : 0 ≤ radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hbroadening : broadening ≠ 0) :
    IntervalIntegrable
      (fun offset : ℝ =>
        ((zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
          targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset)
      volume (-radius) radius := by
  have herror := intervalIntegrable_targetCenteredInterbandSpectatorCurrentErrorIntegrand
    band e v m px py radius broadening hradiusNonneg hradius hbroadening
  apply herror.mono_fun
  · have hocc : Measurable (fun offset : ℝ =>
        ((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m px py + offset) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (measurable_targetCenteredZeroTemperatureOccupation
          (bandEnergy band v m px py) fermiEnergy)
    exact hocc.aestronglyMeasurable.mul herror.def'.aestronglyMeasurable
  · filter_upwards with offset
    rw [norm_mul]
    calc
      ‖((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m px py + offset) : ℝ) : ℂ)‖ *
          ‖targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset‖ ≤
        1 * ‖targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_zeroTemperatureOccupation_complex_le_one
              fermiEnergy (bandEnergy band v m px py + offset)) (norm_nonneg _)
      _ = ‖targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset‖ := one_mul _

/-- The weighted regular pole integral splits exactly into the weighted spectator error plus the
scalar zero-temperature Lorentzian mass multiplying the pole value. -/
theorem targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral_eq_error_add_mass_smul_pole
    (band : Band) (e v m px py fermiEnergy radius broadening : ℝ)
    (hradiusNonneg : 0 ≤ radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hbroadening : broadening ≠ 0) :
    targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
        band e v m px py fermiEnergy radius broadening =
      targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
          band e v m px py fermiEnergy radius broadening +
        targetCenteredZeroTemperatureLorentzianMass
          (bandEnergy band v m px py) fermiEnergy radius broadening •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0) := by
  have herrorInt :=
    intervalIntegrable_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegrand
      band e v m px py fermiEnergy radius broadening
      hradiusNonneg hradius hbroadening
  have hmassInt := intervalIntegrable_targetCenteredZeroTemperatureLorentzianIntegrand
    (bandEnergy band v m px py) fermiEnergy (-radius) radius broadening hbroadening
  have hpoleInt : IntervalIntegrable
      (fun offset : ℝ =>
        (zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) *
          lorentzianSpectralKernel offset broadening) •
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (0, 0))
      volume (-radius) radius := by
    exact hmassInt.smul_continuousOn
      (g := fun _ : ℝ => targetCenteredInterbandSpectatorCurrentFactor
        band e v m px py (0, 0)) continuousOn_const
  unfold targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
  calc
    (∫ offset in -radius..radius,
        ((zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
          ((lorentzianSpectralKernel offset broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (offset, broadening))) =
      ∫ offset in -radius..radius,
        (((zeroTemperatureOccupation fermiEnergy
            (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
          targetCenteredInterbandSpectatorCurrentErrorIntegrand
            band e v m px py broadening offset) +
          (zeroTemperatureOccupation fermiEnergy
              (bandEnergy band v m px py + offset) *
            lorentzianSpectralKernel offset broadening) •
              targetCenteredInterbandSpectatorCurrentFactor
                band e v m px py (0, 0) := by
        apply intervalIntegral.integral_congr
        intro offset _
        unfold targetCenteredInterbandSpectatorCurrentErrorIntegrand
          targetCenteredInterbandSpectatorCurrentError
        change
          ((zeroTemperatureOccupation fermiEnergy
              (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
              ((lorentzianSpectralKernel offset broadening : ℂ) *
                targetCenteredInterbandSpectatorCurrentFactor
                  band e v m px py (offset, broadening)) =
            ((zeroTemperatureOccupation fermiEnergy
                (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
              ((lorentzianSpectralKernel offset broadening : ℂ) *
                (targetCenteredInterbandSpectatorCurrentFactor
                    band e v m px py (offset, broadening) -
                  targetCenteredInterbandSpectatorCurrentFactor
                    band e v m px py (0, 0))) +
              (zeroTemperatureOccupation fermiEnergy
                  (bandEnergy band v m px py + offset) *
                lorentzianSpectralKernel offset broadening) •
                targetCenteredInterbandSpectatorCurrentFactor
                  band e v m px py (0, 0)
        push_cast
        ring
    _ = (∫ offset in -radius..radius,
          (((zeroTemperatureOccupation fermiEnergy
              (bandEnergy band v m px py + offset) : ℝ) : ℂ) *
            targetCenteredInterbandSpectatorCurrentErrorIntegrand
              band e v m px py broadening offset)) +
        ∫ offset in -radius..radius,
          (zeroTemperatureOccupation fermiEnergy
              (bandEnergy band v m px py + offset) *
            lorentzianSpectralKernel offset broadening) •
              targetCenteredInterbandSpectatorCurrentFactor
                band e v m px py (0, 0) := by
        exact intervalIntegral.integral_add herrorInt hpoleInt
    _ = targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
          band e v m px py fermiEnergy radius broadening +
        targetCenteredZeroTemperatureLorentzianMass
          (bandEnergy band v m px py) fermiEnergy radius broadening •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0) := by
        unfold targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
          targetCenteredZeroTemperatureLorentzianMass
        rw [intervalIntegral.integral_smul_const]

/-- The complete zero-temperature weighted regular pole integral converges to the unified scalar pole
weight multiplying the regular factor at the target pole. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
          band e v m px py fermiEnergy radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroTemperatureLorentzianPoleWeight
        fermiEnergy (bandEnergy band v m px py) •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0))) := by
  have herror :=
    tendsto_targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral_zero
      band e v m px py fermiEnergy radius hE hradiusPos hradius
  have hmass := tendsto_targetCenteredZeroTemperatureLorentzianMass_band
    band v m px py fermiEnergy radius hradiusPos
  have hmassPole := hmass.smul_const
    (targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
  have hmain := herror.add hmassPole
  have heq :
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
          band e v m px py fermiEnergy radius broadening) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureInterbandSpectatorCurrentErrorIntegral
            band e v m px py fermiEnergy radius broadening +
          targetCenteredZeroTemperatureLorentzianMass
              (bandEnergy band v m px py) fermiEnergy radius broadening •
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (0, 0)) := by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral_eq_error_add_mass_smul_pole
      band e v m px py fermiEnergy radius broadening hradiusPos.le hradius hbroadening.ne'
  simpa using hmain.congr' heq.symm

/-- Restoring the exact `-2 i` Bastin factor gives the full pointwise zero-temperature weighted pair
limit, including the exact half-weight at the Fermi surface. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((-2 * Complex.I) *
        (zeroTemperatureLorentzianPoleWeight
          fermiEnergy (bandEnergy band v m px py) •
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (0, 0)))) := by
  have hpole := tendsto_targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
    band e v m px py fermiEnergy radius hE hradiusPos hradius
  have hscaled := tendsto_const_nhds.mul hpole
  have heq :
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun broadening : ℝ =>
        (-2 * Complex.I) *
          targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
            band e v m px py fermiEnergy radius broadening) := by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact targetCenteredZeroTemperatureInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
      band e v m px py fermiEnergy radius broadening hbroadening.ne'
  exact hscaled.congr' heq.symm

end

end AnomalousHall.MassiveDirac
