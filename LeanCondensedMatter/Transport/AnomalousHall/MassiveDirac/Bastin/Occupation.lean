import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Lorentzian
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureOccupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature occupation bridge for the massive-Dirac Bastin kernel

The model-independent zero-temperature occupation and Lorentzian finite-window theory live in
`Transport.Analysis.ZeroTemperatureOccupation`.  This module keeps the historical massive-Dirac
names as thin compatibility wrappers and retains only the band-energy specializations in the model
layer.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Compatibility alias for the generic zero-temperature occupation. -/
abbrev zeroTemperatureOccupation := QuantumTheory.Transport.zeroTemperatureOccupation

@[simp] theorem zeroTemperatureOccupation_eq_one
    {fermiEnergy energy : ℝ} (h : energy < fermiEnergy) :
    zeroTemperatureOccupation fermiEnergy energy = 1 :=
  QuantumTheory.Transport.zeroTemperatureOccupation_eq_one h

@[simp] theorem zeroTemperatureOccupation_eq_zero
    {fermiEnergy energy : ℝ} (h : fermiEnergy ≤ energy) :
    zeroTemperatureOccupation fermiEnergy energy = 0 :=
  QuantumTheory.Transport.zeroTemperatureOccupation_eq_zero h

/-- Compatibility wrapper for the generic constant-weight Lorentzian extraction theorem. -/
theorem integral_weight_mul_lorentzian_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius broadening : ℝ)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    (∫ energy in center - radius..center + radius,
        weight energy * lorentzianSpectralKernel (energy - center) broadening) =
      value * (∫ offset in -radius..radius,
        lorentzianSpectralKernel offset broadening) :=
  QuantumTheory.Transport.integral_weight_mul_lorentzian_of_eq_const_on
    weight center value radius broadening hweight

/-- Compatibility wrapper for the generic local-constant Lorentzian mass limit. -/
theorem tendsto_integral_weight_mul_lorentzian_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius : ℝ) (hradius : 0 < radius)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          weight energy * lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (value * Real.pi)) :=
  QuantumTheory.Transport.tendsto_integral_weight_mul_lorentzian_of_eq_const_on
    weight center value radius hradius hweight

/-- Below the Fermi level, the generic centered-window lemma specialized to a band energy. -/
theorem zeroTemperatureOccupation_eq_one_on_band_window
    (band : Band) (v m px py fermiEnergy : ℝ)
    (hoccupied : bandEnergy band v m px py < fermiEnergy) :
    ∀ energy ∈ Set.uIcc
      (bandEnergy band v m px py -
        (fermiEnergy - bandEnergy band v m px py) / 2)
      (bandEnergy band v m px py +
        (fermiEnergy - bandEnergy band v m px py) / 2),
      zeroTemperatureOccupation fermiEnergy energy = 1 :=
  QuantumTheory.Transport.zeroTemperatureOccupation_eq_one_on_center_window
    (bandEnergy band v m px py) fermiEnergy hoccupied

/-- Above the Fermi level, the generic centered-window lemma specialized to a band energy. -/
theorem zeroTemperatureOccupation_eq_zero_on_band_window
    (band : Band) (v m px py fermiEnergy : ℝ)
    (hunoccupied : fermiEnergy < bandEnergy band v m px py) :
    ∀ energy ∈ Set.uIcc
      (bandEnergy band v m px py -
        (bandEnergy band v m px py - fermiEnergy) / 2)
      (bandEnergy band v m px py +
        (bandEnergy band v m px py - fermiEnergy) / 2),
      zeroTemperatureOccupation fermiEnergy energy = 0 :=
  QuantumTheory.Transport.zeroTemperatureOccupation_eq_zero_on_center_window
    (bandEnergy band v m px py) fermiEnergy hunoccupied

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
  exact QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_occupied_finite_window
    (bandEnergy band v m px py) fermiEnergy
    ((fermiEnergy - bandEnergy band v m px py) / 2) hradius hoccupied

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
  exact QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_finite_window
    (bandEnergy band v m px py) fermiEnergy
    ((bandEnergy band v m px py - fermiEnergy) / 2) hradius hunoccupied

end

end AnomalousHall.MassiveDirac
