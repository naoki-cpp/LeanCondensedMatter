import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature Lorentzian occupation weights

This module owns the model-independent zero-temperature step occupation and its interaction with the
scalar Lorentzian approximate identity.  It records local occupied/unoccupied windows, exact
finite-window truncation at the Fermi level, and the unified isolated-pole weights
`π`, `0`, and `π / 2` for occupied, unoccupied, and exact-Fermi poles.

No Hamiltonian, band structure, current operator, or concrete transport model appears here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter MeasureTheory

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
      change weight energy * lorentzianSpectralKernel (energy - center) broadening =
        value * lorentzianSpectralKernel (energy - center) broadening
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

/-- If the Fermi energy lies in a fixed symmetric window, zero-temperature occupation truncates the
Lorentzian energy integral exactly at the Fermi energy. The strict-vs-nonstrict endpoint difference
is a singleton and hence invisible to Lebesgue integration. -/
theorem integral_zeroTemperatureOccupation_mul_lorentzian_of_fermi_mem
    (center fermiEnergy radius broadening : ℝ)
    (hleft : center - radius ≤ fermiEnergy)
    (hright : fermiEnergy ≤ center + radius) :
    (∫ energy in center - radius..center + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - center) broadening) =
      ∫ energy in center - radius..fermiEnergy,
        lorentzianSpectralKernel (energy - center) broadening := by
  calc
    (∫ energy in center - radius..center + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - center) broadening) =
        ∫ energy in center - radius..center + radius,
          Set.indicator {energy : ℝ | energy ≤ fermiEnergy}
            (fun energy => lorentzianSpectralKernel (energy - center) broadening) energy := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne fermiEnergy] with energy hne
      intro _
      by_cases hlt : energy < fermiEnergy
      · simp [zeroTemperatureOccupation, hlt, hlt.le]
      · have hgt : fermiEnergy < energy :=
          lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
        simp [zeroTemperatureOccupation, hlt, not_le.mpr hgt]
    _ = ∫ energy in center - radius..fermiEnergy,
        lorentzianSpectralKernel (energy - center) broadening := by
      exact intervalIntegral.integral_indicator ⟨hleft, hright⟩

/-- Exact arctangent form of the Fermi-truncated finite-window integral. -/
theorem integral_zeroTemperatureOccupation_mul_lorentzian_eq_arctan_of_fermi_mem
    (center fermiEnergy radius broadening : ℝ)
    (hleft : center - radius ≤ fermiEnergy)
    (hright : fermiEnergy ≤ center + radius) :
    (∫ energy in center - radius..center + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - center) broadening) =
      Real.arctan ((fermiEnergy - center) / broadening) +
        Real.arctan (radius / broadening) := by
  rw [integral_zeroTemperatureOccupation_mul_lorentzian_of_fermi_mem
    center fermiEnergy radius broadening hleft hright]
  calc
    (∫ energy in center - radius..fermiEnergy,
        lorentzianSpectralKernel (energy - center) broadening) =
        ∫ offset in -radius..fermiEnergy - center,
          lorentzianSpectralKernel offset broadening := by
      let f : ℝ → ℝ := fun offset => lorentzianSpectralKernel offset broadening
      have hshift := intervalIntegral.integral_comp_sub_right
        (a := center - radius) (b := fermiEnergy) f center
      rw [show center - radius - center = -radius by ring] at hshift
      exact hshift
    _ = Real.arctan ((fermiEnergy - center) / broadening) +
        Real.arctan (radius / broadening) := by
      rw [integral_lorentzianSpectralKernel]
      rw [show (-radius) / broadening = -(radius / broadening) by ring,
        Real.arctan_neg]
      ring

private theorem tendsto_arctan_neg_div_broadening
    (distance : ℝ) (hdistance : distance < 0) :
    Tendsto
      (fun broadening : ℝ => Real.arctan (distance / broadening))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-Real.pi / 2)) := by
  have h := tendsto_arctan_pos_div_broadening (-distance) (neg_pos.mpr hdistance)
  have hneg := h.neg
  simpa only [neg_div, Real.arctan_neg, neg_neg] using hneg

/-- Every fixed positive symmetric energy window around an occupied pole captures asymptotic
zero-temperature Lorentzian weight `π`, whether or not the window crosses the Fermi level. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_occupied_finite_window
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hoccupied : center < fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  by_cases hright : fermiEnergy ≤ center + radius
  · have hleft : center - radius ≤ fermiEnergy := by linarith
    have hfermi := tendsto_arctan_pos_div_broadening
      (fermiEnergy - center) (by linarith)
    have hradius' := tendsto_arctan_pos_div_broadening radius hradius
    have hsum := hfermi.add hradius'
    have hfun :
        (fun broadening : ℝ =>
          ∫ energy in center - radius..center + radius,
            zeroTemperatureOccupation fermiEnergy energy *
              lorentzianSpectralKernel (energy - center) broadening) =
        (fun broadening : ℝ =>
          Real.arctan ((fermiEnergy - center) / broadening) +
            Real.arctan (radius / broadening)) := by
      funext broadening
      exact integral_zeroTemperatureOccupation_mul_lorentzian_eq_arctan_of_fermi_mem
        center fermiEnergy radius broadening hleft hright
    have hpi : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
    rw [hfun]
    rw [hpi] at hsum
    exact hsum
  · have hbounds : center - radius ≤ center + radius := by linarith
    have hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
        zeroTemperatureOccupation fermiEnergy energy = 1 := by
      intro energy henergy
      rw [Set.uIcc_of_le hbounds] at henergy
      apply zeroTemperatureOccupation_eq_one
      exact lt_of_le_of_lt henergy.2 (lt_of_not_ge hright)
    have h := tendsto_integral_weight_mul_lorentzian_of_eq_const_on
      (zeroTemperatureOccupation fermiEnergy) center 1 radius hradius hweight
    simpa using h

/-- Every fixed positive symmetric energy window around an unoccupied pole has asymptotic
zero-temperature Lorentzian weight `0`, whether or not the window crosses the Fermi level. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_finite_window
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hunoccupied : fermiEnergy < center) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  by_cases hleft : center - radius ≤ fermiEnergy
  · have hright : fermiEnergy ≤ center + radius := by linarith
    have hfermi := tendsto_arctan_neg_div_broadening
      (fermiEnergy - center) (by linarith)
    have hradius' := tendsto_arctan_pos_div_broadening radius hradius
    have hsum := hfermi.add hradius'
    have hfun :
        (fun broadening : ℝ =>
          ∫ energy in center - radius..center + radius,
            zeroTemperatureOccupation fermiEnergy energy *
              lorentzianSpectralKernel (energy - center) broadening) =
        (fun broadening : ℝ =>
          Real.arctan ((fermiEnergy - center) / broadening) +
            Real.arctan (radius / broadening)) := by
      funext broadening
      exact integral_zeroTemperatureOccupation_mul_lorentzian_eq_arctan_of_fermi_mem
        center fermiEnergy radius broadening hleft hright
    have hzero : -Real.pi / 2 + Real.pi / 2 = 0 := by ring
    rw [hfun]
    rw [hzero] at hsum
    exact hsum
  · have hbounds : center - radius ≤ center + radius := by linarith
    have hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
        zeroTemperatureOccupation fermiEnergy energy = 0 := by
      intro energy henergy
      rw [Set.uIcc_of_le hbounds] at henergy
      apply zeroTemperatureOccupation_eq_zero
      exact le_trans (le_of_not_ge hleft) henergy.1
    have h := tendsto_integral_weight_mul_lorentzian_of_eq_const_on
      (zeroTemperatureOccupation fermiEnergy) center 0 radius hradius hweight
    simpa using h

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
finite energy window. -/
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

/-- Unified finite-window pole extraction at zero temperature. -/
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

end

end Transport
end QuantumTheory
