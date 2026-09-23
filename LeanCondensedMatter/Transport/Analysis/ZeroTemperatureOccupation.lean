import Mathlib.Data.Complex.Basic

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

end
end Transport
end QuantumTheory
