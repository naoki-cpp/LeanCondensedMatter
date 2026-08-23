import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.FiniteWindow
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact Fermi-surface pole for the massive-Dirac Bastin kernel

The finite-window occupation extraction is complete away from the exact Fermi surface.  At a pole
with `E_n = ε_F`, the strict zero-temperature occupation convention is zero at the endpoint itself,
but that single point is invisible to Lebesgue integration.  A symmetric Lorentzian therefore
captures exactly half of its spectral mass below the Fermi level and contributes asymptotic weight
`π / 2`.

This file records that boundary explicitly and packages occupied, unoccupied, and exact-Fermi poles
into one finite-window theorem.  No momentum integration or interchange of limits is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- On a symmetric window centered exactly at the Fermi energy, zero-temperature occupation keeps
exactly one half of the Lorentzian spectral mass. -/
theorem integral_zeroTemperatureOccupation_lorentzian_fermi_surface_eq_half_mass
    (fermiEnergy radius broadening : ℝ) (hradius : 0 ≤ radius) :
    (∫ energy in fermiEnergy - radius..fermiEnergy + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - fermiEnergy) broadening) =
      (1 / 2 : ℝ) *
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) := by
  rw [integral_zeroTemperatureOccupation_mul_lorentzian_eq_arctan_of_fermi_mem
    fermiEnergy fermiEnergy radius broadening (by linarith) (by linarith),
    integral_lorentzianSpectralKernel_symmetric]
  simp

/-- An exact Fermi-surface pole contributes half of the full Lorentzian mass in every fixed positive
symmetric window. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_fermi_surface_finite_window
    (fermiEnergy radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in fermiEnergy - radius..fermiEnergy + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - fermiEnergy) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  have hmass := tendsto_integral_lorentzianSpectralKernel_symmetric radius hradius
  have hhalf :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ))).mul hmass
  have hfun :
      (fun broadening : ℝ =>
        ∫ energy in fermiEnergy - radius..fermiEnergy + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - fermiEnergy) broadening) =
      (fun broadening : ℝ =>
        (1 / 2 : ℝ) *
          (∫ offset in -radius..radius,
            lorentzianSpectralKernel offset broadening)) := by
    funext broadening
    exact integral_zeroTemperatureOccupation_lorentzian_fermi_surface_eq_half_mass
      fermiEnergy radius broadening hradius.le
  rw [hfun]
  convert hhalf using 1
  ring

/-- The asymptotic zero-temperature Lorentzian weight assigned to an isolated pole on a symmetric
finite energy window.  Occupied, unoccupied, and exact-Fermi poles carry weights `π`, `0`, and
`π / 2`, respectively. -/
def zeroTemperatureLorentzianPoleWeight (fermiEnergy center : ℝ) : ℝ :=
  if center < fermiEnergy then Real.pi
  else if fermiEnergy < center then 0
  else Real.pi / 2

@[simp] theorem zeroTemperatureLorentzianPoleWeight_of_occupied
    {fermiEnergy center : ℝ} (h : center < fermiEnergy) :
    zeroTemperatureLorentzianPoleWeight fermiEnergy center = Real.pi := by
  simp [zeroTemperatureLorentzianPoleWeight, h]

@[simp] theorem zeroTemperatureLorentzianPoleWeight_of_unoccupied
    {fermiEnergy center : ℝ} (h : fermiEnergy < center) :
    zeroTemperatureLorentzianPoleWeight fermiEnergy center = 0 := by
  simp [zeroTemperatureLorentzianPoleWeight, h, not_lt.mpr h.le]

@[simp] theorem zeroTemperatureLorentzianPoleWeight_at_fermi_surface
    (fermiEnergy : ℝ) :
    zeroTemperatureLorentzianPoleWeight fermiEnergy fermiEnergy = Real.pi / 2 := by
  simp [zeroTemperatureLorentzianPoleWeight]

/-- Unified finite-window pole extraction at zero temperature.  The theorem makes the exact
Fermi-surface half-weight explicit instead of hiding it inside a convention for the point value of
the occupation function. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_finite_window
    (center fermiEnergy radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroTemperatureLorentzianPoleWeight fermiEnergy center)) := by
  rcases lt_trichotomy center fermiEnergy with hoccupied | heq | hunoccupied
  · simpa [zeroTemperatureLorentzianPoleWeight, hoccupied] using
      tendsto_zeroTemperatureOccupation_lorentzian_occupied_finite_window
        center fermiEnergy radius hradius hoccupied
  · subst fermiEnergy
    simpa [zeroTemperatureLorentzianPoleWeight] using
      tendsto_zeroTemperatureOccupation_lorentzian_fermi_surface_finite_window
        center radius hradius
  · simpa [zeroTemperatureLorentzianPoleWeight, hunoccupied,
      not_lt.mpr hunoccupied.le] using
      tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_finite_window
        center fermiEnergy radius hradius hunoccupied

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
  exact tendsto_zeroTemperatureOccupation_lorentzian_fermi_surface_finite_window
    (bandEnergy band v m px py) radius hradius

end

end AnomalousHall.MassiveDirac
