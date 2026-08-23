import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Tail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-window zero-temperature extraction for the massive-Dirac Bastin kernel

The local pole extraction and Lorentzian tail control now allow the zero-temperature energy
integral to be treated on an arbitrary fixed positive symmetric window around a band energy.
Because the zero-temperature occupation is a step function, the cleanest finite-window argument is
to truncate the interval exactly at the Fermi energy rather than introduce a general weighted
distribution theorem.

Away from the exact Fermi-surface case, every fixed positive symmetric window therefore has the
expected zero-broadening limit: an occupied pole contributes `π`, while an unoccupied pole
contributes `0`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory

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

private theorem tendsto_arctan_pos_div_broadening
    (distance : ℝ) (hdistance : 0 < distance) :
    Tendsto
      (fun broadening : ℝ => Real.arctan (distance / broadening))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  have hinv : Tendsto (fun broadening : ℝ => broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hscaled : Tendsto (fun broadening : ℝ => distance * broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => distance)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds distance)).pos_mul_atTop hdistance hinv
  have harctanWithin := Real.tendsto_arctan_atTop.comp hscaled
  have harctan := tendsto_nhds_of_tendsto_nhdsWithin harctanWithin
  change Tendsto
    (fun broadening : ℝ => Real.arctan (distance * broadening⁻¹))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) at harctan
  simpa only [div_eq_mul_inv] using harctan

private theorem tendsto_arctan_neg_div_broadening
    (distance : ℝ) (hdistance : distance < 0) :
    Tendsto
      (fun broadening : ℝ => Real.arctan (distance / broadening))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-Real.pi / 2)) := by
  have h := tendsto_arctan_pos_div_broadening (-distance) (neg_pos.mpr hdistance)
  have hneg := h.neg
  simpa only [neg_div, Real.arctan_neg, neg_neg] using hneg

/-- If an occupied pole's finite symmetric window reaches the Fermi level, its zero-temperature
Lorentzian weight still tends to `π`. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_occupied_of_fermi_mem
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hoccupied : center < fermiEnergy)
    (hright : fermiEnergy ≤ center + radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have hleft : center - radius ≤ fermiEnergy := by linarith
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

/-- If an unoccupied pole's finite symmetric window reaches the Fermi level, only a Lorentzian tail
is occupied and its zero-broadening weight tends to `0`. -/
theorem tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_of_fermi_mem
    (center fermiEnergy radius : ℝ)
    (hradius : 0 < radius) (hunoccupied : fermiEnergy < center)
    (hleft : center - radius ≤ fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hright : fermiEnergy ≤ center + radius := by linarith
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
  · exact tendsto_zeroTemperatureOccupation_lorentzian_occupied_of_fermi_mem
      center fermiEnergy radius hradius hoccupied hright
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
  · exact tendsto_zeroTemperatureOccupation_lorentzian_unoccupied_of_fermi_mem
      center fermiEnergy radius hradius hunoccupied hleft
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

end

end AnomalousHall.MassiveDirac
