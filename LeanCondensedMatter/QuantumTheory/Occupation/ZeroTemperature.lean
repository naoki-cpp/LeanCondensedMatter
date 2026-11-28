import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Zero-temperature spectral occupation

This module owns the model-independent strict zero-temperature Fermi step and its pointwise basic
properties. States below the Fermi energy are occupied and states at or above it are empty.

Band-filling predicates are owned by `QuantumTheory.Occupation.BandFilling`.
Lorentzian finite-window and broadening-limit analysis remains downstream in
`Transport.Analysis.ZeroTemperatureLorentzian`. Neither is required to define the scalar law.
-/

namespace QuantumTheory

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

/-- Unit occupation is equivalent to lying strictly below the Fermi energy. -/
@[simp] theorem zeroTemperatureOccupation_eq_one_iff (fermiEnergy energy : ℝ) :
    zeroTemperatureOccupation fermiEnergy energy = 1 ↔ energy < fermiEnergy := by
  by_cases h : energy < fermiEnergy <;> simp [zeroTemperatureOccupation, h]

/-- Zero occupation is equivalent to lying at or above the Fermi energy. -/
@[simp] theorem zeroTemperatureOccupation_eq_zero_iff (fermiEnergy energy : ℝ) :
    zeroTemperatureOccupation fermiEnergy energy = 0 ↔ fermiEnergy ≤ energy := by
  by_cases h : energy < fermiEnergy
  · have hnot : ¬ fermiEnergy ≤ energy := not_le_of_gt h
    simp [zeroTemperatureOccupation, h, hnot]
  · have hle : fermiEnergy ≤ energy := le_of_not_gt h
    simp [zeroTemperatureOccupation, h, hle]

/-- The complex norm of the zero-temperature occupation is at most one. -/
theorem norm_zeroTemperatureOccupation_complex_le_one
    (fermiEnergy energy : ℝ) :
    ‖((zeroTemperatureOccupation fermiEnergy energy : ℝ) : ℂ)‖ ≤ 1 := by
  by_cases h : energy < fermiEnergy <;>
    simp [zeroTemperatureOccupation, h]


end
end QuantumTheory
