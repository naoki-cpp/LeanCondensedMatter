import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinLorentzian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature occupation bridge for the massive-Dirac Bastin kernel

The Lorentzian spectral weight from `MassiveDiracBastinLorentzian` already carries asymptotic mass
`π` in every fixed positive symmetric neighborhood.  For the metallic zero-temperature benchmark,
the occupation is locally constant at a band energy whenever that band energy is separated from
the Fermi level.  This file records that local-constant extraction directly, without introducing a
general distribution theorem or interchanging an unsupported limit with an energy integral.

The exact Fermi-surface case remains separate: no statement below applies when a band energy equals
the Fermi level.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Zero-temperature occupation convention used by the clean metallic benchmark. -/
def zeroTemperatureOccupation (fermiEnergy energy : ℝ) : ℝ :=
  if energy < fermiEnergy then 1 else 0

@[simp] theorem zeroTemperatureOccupation_eq_one
    {fermiEnergy energy : ℝ} (h : energy < fermiEnergy) :
    zeroTemperatureOccupation fermiEnergy energy = 1 := by
  simp [zeroTemperatureOccupation, h]

@[simp] theorem zeroTemperatureOccupation_eq_zero
    {fermiEnergy energy : ℝ} (h : fermiEnergy ≤ energy) :
    zeroTemperatureOccupation fermiEnergy energy = 0 := by
  simp [zeroTemperatureOccupation, not_lt.mpr h]

/-- If a weight is constant on the centered integration window, it factors out exactly and the
remaining energy integral is the centered Lorentzian mass. -/
theorem integral_weight_mul_lorentzian_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius broadening : ℝ)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    (∫ energy in center - radius..center + radius,
        weight energy * lorentzianSpectralKernel (energy - center) broadening) =
      value * (∫ offset in -radius..radius,
        lorentzianSpectralKernel offset broadening) := by
  calc
    (∫ energy in center - radius..center + radius,
        weight energy * lorentzianSpectralKernel (energy - center) broadening) =
        ∫ energy in center - radius..center + radius,
          value * lorentzianSpectralKernel (energy - center) broadening := by
      apply intervalIntegral.integral_congr
      intro energy henergy
      rw [hweight energy henergy]
    _ = ∫ offset in -radius..radius,
        value * lorentzianSpectralKernel offset broadening := by
      let f : ℝ → ℝ := fun offset => value * lorentzianSpectralKernel offset broadening
      have hshift := intervalIntegral.integral_comp_sub_right
        (a := center - radius) (b := center + radius) f center
      rw [show center - radius - center = -radius by ring,
        show center + radius - center = radius by ring] at hshift
      exact hshift
    _ = value * (∫ offset in -radius..radius,
        lorentzianSpectralKernel offset broadening) := by
      rw [intervalIntegral.integral_const_mul]

/-- Local-constant weights inherit the `π` Lorentzian mass in the positive zero-broadening limit. -/
theorem tendsto_integral_weight_mul_lorentzian_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius : ℝ) (hradius : 0 < radius)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          weight energy * lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (value * Real.pi)) := by
  have hmass := tendsto_integral_lorentzianSpectralKernel_symmetric radius hradius
  have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => value)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds value)).mul hmass
  have hfun :
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          weight energy * lorentzianSpectralKernel (energy - center) broadening) =
      (fun broadening : ℝ =>
        value * (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening)) := by
    funext broadening
    exact integral_weight_mul_lorentzian_of_eq_const_on
      weight center value radius broadening hweight
  rw [hfun]
  exact hscaled

/-- Below the Fermi level, zero-temperature occupation is identically one on the symmetric window
with radius half the spectral distance to the Fermi level. -/
theorem zeroTemperatureOccupation_eq_one_on_band_window
    (band : Band) (v m px py fermiEnergy : ℝ)
    (hoccupied : bandEnergy band v m px py < fermiEnergy) :
    ∀ energy ∈ Set.uIcc
      (bandEnergy band v m px py -
        (fermiEnergy - bandEnergy band v m px py) / 2)
      (bandEnergy band v m px py +
        (fermiEnergy - bandEnergy band v m px py) / 2),
      zeroTemperatureOccupation fermiEnergy energy = 1 := by
  intro energy henergy
  have hradius : 0 < (fermiEnergy - bandEnergy band v m px py) / 2 := by
    linarith
  have hbounds :
      bandEnergy band v m px py -
          (fermiEnergy - bandEnergy band v m px py) / 2 ≤
        bandEnergy band v m px py +
          (fermiEnergy - bandEnergy band v m px py) / 2 := by
    linarith
  rw [Set.uIcc_of_le hbounds] at henergy
  apply zeroTemperatureOccupation_eq_one
  linarith [henergy.2]

/-- Above the Fermi level, zero-temperature occupation is identically zero on the symmetric window
with radius half the spectral distance to the Fermi level. -/
theorem zeroTemperatureOccupation_eq_zero_on_band_window
    (band : Band) (v m px py fermiEnergy : ℝ)
    (hunoccupied : fermiEnergy < bandEnergy band v m px py) :
    ∀ energy ∈ Set.uIcc
      (bandEnergy band v m px py -
        (bandEnergy band v m px py - fermiEnergy) / 2)
      (bandEnergy band v m px py +
        (bandEnergy band v m px py - fermiEnergy) / 2),
      zeroTemperatureOccupation fermiEnergy energy = 0 := by
  intro energy henergy
  have hradius : 0 < (bandEnergy band v m px py - fermiEnergy) / 2 := by
    linarith
  have hbounds :
      bandEnergy band v m px py -
          (bandEnergy band v m px py - fermiEnergy) / 2 ≤
        bandEnergy band v m px py +
          (bandEnergy band v m px py - fermiEnergy) / 2 := by
    linarith
  rw [Set.uIcc_of_le hbounds] at henergy
  apply zeroTemperatureOccupation_eq_zero
  linarith [henergy.1]

/-- An occupied band pole contributes asymptotic Lorentzian weight `π` away from the Fermi
surface. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_occupied
    (band : Band) (v m px py fermiEnergy : ℝ)
    (hoccupied : bandEnergy band v m px py < fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in
          bandEnergy band v m px py -
              (fermiEnergy - bandEnergy band v m px py) / 2..
            bandEnergy band v m px py +
              (fermiEnergy - bandEnergy band v m px py) / 2,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel
              (energy - bandEnergy band v m px py) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have hradius : 0 < (fermiEnergy - bandEnergy band v m px py) / 2 := by
    linarith
  have h := tendsto_integral_weight_mul_lorentzian_of_eq_const_on
    (zeroTemperatureOccupation fermiEnergy)
    (bandEnergy band v m px py) 1
    ((fermiEnergy - bandEnergy band v m px py) / 2) hradius
    (zeroTemperatureOccupation_eq_one_on_band_window
      band v m px py fermiEnergy hoccupied)
  simpa using h

/-- An unoccupied band pole contributes zero asymptotic Lorentzian weight away from the Fermi
surface. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_unoccupied
    (band : Band) (v m px py fermiEnergy : ℝ)
    (hunoccupied : fermiEnergy < bandEnergy band v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in
          bandEnergy band v m px py -
              (bandEnergy band v m px py - fermiEnergy) / 2..
            bandEnergy band v m px py +
              (bandEnergy band v m px py - fermiEnergy) / 2,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel
              (energy - bandEnergy band v m px py) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hradius : 0 < (bandEnergy band v m px py - fermiEnergy) / 2 := by
    linarith
  have h := tendsto_integral_weight_mul_lorentzian_of_eq_const_on
    (zeroTemperatureOccupation fermiEnergy)
    (bandEnergy band v m px py) 0
    ((bandEnergy band v m px py - fermiEnergy) / 2) hradius
    (zeroTemperatureOccupation_eq_zero_on_band_window
      band v m px py fermiEnergy hunoccupied)
  simpa using h

end

end AnomalousHall.MassiveDirac
