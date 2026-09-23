import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-!
# Zero-temperature spectral occupation

This module owns the model-independent strict zero-temperature Fermi step and its pointwise basic
properties. States below the Fermi energy are occupied and states at or above it are empty.

Band-filling predicates live in `Transport.Analysis.ZeroTemperatureBandFilling`. Lorentzian
finite-window and broadening-limit analysis lives in
`Transport.Analysis.ZeroTemperatureLorentzian`.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Strict zero-temperature occupation convention: states below the Fermi energy are occupied. -/
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

/-- The complex norm of the zero-temperature occupation is at most one. -/
theorem norm_zeroTemperatureOccupation_complex_le_one
    (fermiEnergy energy : ℝ) :
    ‖((zeroTemperatureOccupation fermiEnergy energy : ℝ) : ℂ)‖ ≤ 1 := by
  by_cases h : energy < fermiEnergy <;>
    simp [zeroTemperatureOccupation, h]

/-- Below the Fermi level, zero-temperature occupation is identically one on the symmetric window
with radius half the spectral distance to the Fermi level. -/
theorem zeroTemperatureOccupation_eq_one_on_center_window
    (center fermiEnergy : ℝ) (hoccupied : center < fermiEnergy) :
    ∀ energy ∈ Set.uIcc
      (center - (fermiEnergy - center) / 2)
      (center + (fermiEnergy - center) / 2),
      zeroTemperatureOccupation fermiEnergy energy = 1 := by
  intro energy henergy
  have hbounds :
      center - (fermiEnergy - center) / 2 ≤
        center + (fermiEnergy - center) / 2 := by
    linarith
  rw [Set.uIcc_of_le hbounds] at henergy
  apply zeroTemperatureOccupation_eq_one
  linarith [henergy.2]

/-- Above the Fermi level, zero-temperature occupation is identically zero on the symmetric window
with radius half the spectral distance to the Fermi level. -/
theorem zeroTemperatureOccupation_eq_zero_on_center_window
    (center fermiEnergy : ℝ) (hunoccupied : fermiEnergy < center) :
    ∀ energy ∈ Set.uIcc
      (center - (center - fermiEnergy) / 2)
      (center + (center - fermiEnergy) / 2),
      zeroTemperatureOccupation fermiEnergy energy = 0 := by
  intro energy henergy
  have hbounds :
      center - (center - fermiEnergy) / 2 ≤
        center + (center - fermiEnergy) / 2 := by
    linarith
  rw [Set.uIcc_of_le hbounds] at henergy
  apply zeroTemperatureOccupation_eq_zero
  linarith [henergy.1]

end
end Transport
end QuantumTheory
