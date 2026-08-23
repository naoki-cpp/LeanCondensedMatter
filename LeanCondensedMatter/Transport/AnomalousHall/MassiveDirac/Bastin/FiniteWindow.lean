import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Tail
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-window zero-temperature extraction for the massive-Dirac Bastin kernel

The model-independent finite-window occupation theorems now live in
`Transport.Analysis.ZeroTemperatureOccupation`.  This module preserves the historical
massive-Dirac theorem names as compatibility wrappers while delegating the proof content to the
generic analysis layer.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory

/-- Compatibility wrapper for generic Fermi-level truncation of a finite Lorentzian window. -/
theorem integral_zeroTemperatureOccupation_mul_lorentzian_of_fermi_mem
    (center fermiEnergy radius broadening : ℝ)
    (hleft : center - radius ≤ fermiEnergy)
    (hright : fermiEnergy ≤ center + radius) :
    (∫ energy in center - radius..center + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - center) broadening) =
      ∫ energy in center - radius..fermiEnergy,
        lorentzianSpectralKernel (energy - center) broadening :=
  QuantumTheory.Transport.integral_zeroTemperatureOccupation_mul_lorentzian_of_fermi_mem
    center fermiEnergy radius broadening hleft hright

/-- Compatibility wrapper for the exact arctangent form of the Fermi-truncated window. -/
theorem integral_zeroTemperatureOccupation_mul_lorentzian_eq_arctan_of_fermi_mem
    (center fermiEnergy radius broadening : ℝ)
    (hleft : center - radius ≤ fermiEnergy)
    (hright : fermiEnergy ≤ center + radius) :
    (∫ energy in center - radius..center + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - center) broadening) =
      Real.arctan ((fermiEnergy - center) / broadening) +
        Real.arctan (radius / broadening) :=
  QuantumTheory.Transport.integral_zeroTemperatureOccupation_mul_lorentzian_eq_arctan_of_fermi_mem
    center fermiEnergy radius broadening hleft hright

/-- Historical crossing-window theorem, now implied by the stronger generic finite-window result. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_occupied_of_fermi_mem
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hoccupied : center < fermiEnergy)
    (_hright : fermiEnergy ≤ center + radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) :=
  QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_occupied_finite_window
    center fermiEnergy radius hradius hoccupied

/-- Historical crossing-window theorem, now implied by the stronger generic finite-window result. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_of_fermi_mem
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hunoccupied : fermiEnergy < center)
    (_hleft : center - radius ≤ fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
  QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_finite_window
    center fermiEnergy radius hradius hunoccupied

/-- Every fixed positive symmetric energy window around an occupied pole captures asymptotic
zero-temperature Lorentzian weight `π`. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_occupied_finite_window
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hoccupied : center < fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) :=
  QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_occupied_finite_window
    center fermiEnergy radius hradius hoccupied

/-- Every fixed positive symmetric energy window around an unoccupied pole has asymptotic
zero-temperature Lorentzian weight `0`. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_finite_window
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hunoccupied : fermiEnergy < center) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
  QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_finite_window
    center fermiEnergy radius hradius hunoccupied

end

end AnomalousHall.MassiveDirac
