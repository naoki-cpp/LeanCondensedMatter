import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceEnergyKernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian split of the massive-Dirac Středa surface density

The positive-energy Středa surface density admits an exact partial-fraction decomposition into a
Fermi-centered Lorentzian minus a mirror Lorentzian centered at negative Fermi energy. This makes
the clean limit transparent: on a positive-energy interval containing `εF`, the first Lorentzian
carries mass `π`, while the mirror term carries no mass.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Exact partial-fraction decomposition of the positive-energy Středa surface density. -/
theorem stredaSurfaceRadialEnergyDensity_eq_lorentzian_difference
    (e m fermiEnergy energy broadening : ℝ)
    (hfermi : fermiEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    stredaSurfaceRadialEnergyDensity e m fermiEnergy energy broadening =
      -(e ^ 2 * m / fermiEnergy) *
        (lorentzianSpectralKernel (energy - fermiEnergy) broadening -
          lorentzianSpectralKernel (energy + fermiEnergy) broadening) := by
  have hdenSurfacePlus :
      (fermiEnergy + energy) ^ 2 + broadening ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hdenSurfaceMinus :
      (fermiEnergy - energy) ^ 2 + broadening ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hdenLorentzMinus :
      broadening ^ 2 + (energy - fermiEnergy) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hdenLorentzPlus :
      broadening ^ 2 + (energy + fermiEnergy) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  unfold stredaSurfaceRadialEnergyDensity lorentzianSpectralKernel
  field_simp [hfermi, hdenSurfacePlus, hdenSurfaceMinus,
    hdenLorentzMinus, hdenLorentzPlus]
  ring

/-- Shifted finite-interval Lorentzian integral in arctangent form. -/
theorem integral_lorentzianSpectralKernel_sub_center_eq_arctan
    (center lower upper broadening : ℝ) :
    (∫ energy in lower..upper,
      lorentzianSpectralKernel (energy - center) broadening) =
      Real.arctan ((upper - center) / broadening) -
        Real.arctan ((lower - center) / broadening) := by
  let f : ℝ → ℝ := fun offset => lorentzianSpectralKernel offset broadening
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := lower) (b := upper) f center
  calc
    (∫ energy in lower..upper,
      lorentzianSpectralKernel (energy - center) broadening) =
        ∫ offset in lower - center..upper - center,
          lorentzianSpectralKernel offset broadening := hshift
    _ = Real.arctan ((upper - center) / broadening) -
        Real.arctan ((lower - center) / broadening) := by
      exact integral_lorentzianSpectralKernel
        (lower - center) (upper - center) broadening

private theorem tendsto_arctan_pos_div_zero
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

private theorem tendsto_arctan_neg_div_zero
    (distance : ℝ) (hdistance : distance < 0) :
    Tendsto
      (fun broadening : ℝ => Real.arctan (distance / broadening))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-Real.pi / 2)) := by
  have h := tendsto_arctan_pos_div_zero (-distance) (neg_pos.mpr hdistance)
  have hneg := h.neg
  simpa only [neg_div, Real.arctan_neg, neg_neg] using hneg

/-- A Lorentzian centered strictly inside a fixed interval contributes asymptotic mass `π`. -/
theorem tendsto_integral_lorentzianSpectralKernel_sub_center_of_mem
    (center lower upper : ℝ) (hlower : lower < center) (hupper : center < upper) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in lower..upper,
          lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have hu := tendsto_arctan_pos_div_zero (upper - center) (by linarith)
  have hl := tendsto_arctan_neg_div_zero (lower - center) (by linarith)
  have hsub := hu.sub hl
  have hlimit : Real.pi / 2 - (-Real.pi / 2) = Real.pi := by ring
  have hfun :
      (fun broadening : ℝ =>
        ∫ energy in lower..upper,
          lorentzianSpectralKernel (energy - center) broadening) =
      (fun broadening : ℝ =>
        Real.arctan ((upper - center) / broadening) -
          Real.arctan ((lower - center) / broadening)) := by
    funext broadening
    exact integral_lorentzianSpectralKernel_sub_center_eq_arctan
      center lower upper broadening
  rw [hfun]
  rw [hlimit] at hsub
  exact hsub

/-- A Lorentzian whose center lies strictly below a fixed interval has vanishing clean mass. -/
theorem tendsto_integral_lorentzianSpectralKernel_sub_center_of_center_lt_lower
    (center lower upper : ℝ) (hcenter : center < lower) (hlowerUpper : lower ≤ upper) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in lower..upper,
          lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hl := tendsto_arctan_pos_div_zero (lower - center) (by linarith)
  have hu := tendsto_arctan_pos_div_zero (upper - center) (by linarith)
  have hsub := hu.sub hl
  have hlimit : Real.pi / 2 - Real.pi / 2 = 0 := by ring
  have hfun :
      (fun broadening : ℝ =>
        ∫ energy in lower..upper,
          lorentzianSpectralKernel (energy - center) broadening) =
      (fun broadening : ℝ =>
        Real.arctan ((upper - center) / broadening) -
          Real.arctan ((lower - center) / broadening)) := by
    funext broadening
    exact integral_lorentzianSpectralKernel_sub_center_eq_arctan
      center lower upper broadening
  rw [hfun]
  rw [hlimit] at hsub
  exact hsub

end

end AnomalousHall.MassiveDirac
