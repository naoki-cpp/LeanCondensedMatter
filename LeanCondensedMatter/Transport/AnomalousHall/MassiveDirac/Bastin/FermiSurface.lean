import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.FiniteWindow
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact Fermi-surface pole for the massive-Dirac Bastin kernel

The exact Fermi-edge half-weight and unified zero-temperature Lorentzian pole-weight theorem now
live in `Transport.Analysis.ZeroTemperatureOccupation`.  This module preserves the historical
massive-Dirac names as compatibility wrappers and keeps only the band-energy specialization in the
model layer.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Compatibility wrapper for the generic exact half-mass identity at the Fermi surface. -/
theorem integral_zeroTemperatureOccupation_lorentzian_fermi_surface_eq_half_mass
    (fermiEnergy radius broadening : ℝ) (hradius : 0 ≤ radius) :
    (∫ energy in fermiEnergy - radius..fermiEnergy + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - fermiEnergy) broadening) =
      (1 / 2 : ℝ) *
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) :=
  QuantumTheory.Transport.integral_zeroTemperatureOccupation_lorentzian_fermi_surface_eq_half_mass
    fermiEnergy radius broadening hradius

/-- Compatibility wrapper for the generic exact-Fermi finite-window limit. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_fermi_surface_finite_window
    (fermiEnergy radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in fermiEnergy - radius..fermiEnergy + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - fermiEnergy) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) :=
  QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_fermi_surface_finite_window
    fermiEnergy radius hradius

/-- Compatibility alias for the generic zero-temperature isolated-pole weight. -/
abbrev zeroTemperatureLorentzianPoleWeight :=
  QuantumTheory.Transport.zeroTemperatureLorentzianPoleWeight

@[simp] theorem zeroTemperatureLorentzianPoleWeight_of_occupied
    {fermiEnergy center : ℝ} (h : center < fermiEnergy) :
    zeroTemperatureLorentzianPoleWeight fermiEnergy center = Real.pi :=
  QuantumTheory.Transport.zeroTemperatureLorentzianPoleWeight_of_occupied h

@[simp] theorem zeroTemperatureLorentzianPoleWeight_of_unoccupied
    {fermiEnergy center : ℝ} (h : fermiEnergy < center) :
    zeroTemperatureLorentzianPoleWeight fermiEnergy center = 0 :=
  QuantumTheory.Transport.zeroTemperatureLorentzianPoleWeight_of_unoccupied h

@[simp] theorem zeroTemperatureLorentzianPoleWeight_at_fermi_surface
    (fermiEnergy : ℝ) :
    zeroTemperatureLorentzianPoleWeight fermiEnergy fermiEnergy = Real.pi / 2 :=
  QuantumTheory.Transport.zeroTemperatureLorentzianPoleWeight_at_fermi_surface fermiEnergy

/-- Compatibility wrapper for the unified generic `π / 0 / π/2` finite-window pole theorem. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_finite_window
    (center fermiEnergy radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroTemperatureLorentzianPoleWeight fermiEnergy center)) :=
  QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_finite_window
    center fermiEnergy radius hradius

/-- Band-energy specialization of the exact Fermi-surface half-weight theorem. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_band_at_fermi_surface
    (band : Band) (v m px py fermiEnergy radius : ℝ)
    (hradius : 0 < radius)
    (hfermi : bandEnergy band v m px py = fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in bandEnergy band v m px py - radius..
            bandEnergy band v m px py + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel
              (energy - bandEnergy band v m px py) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  subst fermiEnergy
  exact QuantumTheory.Transport.tendsto_zeroTemperatureOccupation_lorentzian_fermi_surface_finite_window
    (bandEnergy band v m px py) radius hradius

end

end AnomalousHall.MassiveDirac
