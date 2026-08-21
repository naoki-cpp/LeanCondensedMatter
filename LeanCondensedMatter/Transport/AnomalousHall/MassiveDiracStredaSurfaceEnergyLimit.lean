import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceLorentzianSplit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Clean positive-energy limit of the massive-Dirac Středa surface term

After the exact Lorentzian split, the Fermi-centered Lorentzian contributes mass `π` while the
mirror Lorentzian centered at `-εF` vanishes on the positive-energy integration interval. This file
combines those two facts into the clean limit of the finite positive-energy Středa surface integral.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

private theorem continuous_lorentzianSpectralKernel_sub_center
    (center broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (fun energy : ℝ =>
      lorentzianSpectralKernel (energy - center) broadening) := by
  unfold lorentzianSpectralKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add ((continuous_id.sub continuous_const).pow 2))
    (fun energy => by
      nlinarith [sq_pos_of_ne_zero hbroadening])

/-- Exact representation of the finite positive-energy Středa surface integral as the difference
of the Fermi-centered and mirror Lorentzian masses. -/
theorem finiteEnergyStredaSurfaceIntegral_eq_lorentzian_difference
    (e m fermiEnergy energyMax broadening : ℝ)
    (hfermi : fermiEnergy ≠ 0) (hbroadening : broadening ≠ 0) :
    finiteEnergyStredaSurfaceIntegral e m fermiEnergy energyMax broadening =
      -(e ^ 2 * m / fermiEnergy) *
        ((∫ energy in m..energyMax,
            lorentzianSpectralKernel (energy - fermiEnergy) broadening) -
          ∫ energy in m..energyMax,
            lorentzianSpectralKernel (energy + fermiEnergy) broadening) := by
  have hIntFermi : IntervalIntegrable
      (fun energy : ℝ =>
        lorentzianSpectralKernel (energy - fermiEnergy) broadening)
      volume m energyMax :=
    (continuous_lorentzianSpectralKernel_sub_center
      fermiEnergy broadening hbroadening).intervalIntegrable _ _
  have hIntMirror : IntervalIntegrable
      (fun energy : ℝ =>
        lorentzianSpectralKernel (energy - (-fermiEnergy)) broadening)
      volume m energyMax :=
    (continuous_lorentzianSpectralKernel_sub_center
      (-fermiEnergy) broadening hbroadening).intervalIntegrable _ _
  unfold finiteEnergyStredaSurfaceIntegral
  calc
    (∫ energy in m..energyMax,
      stredaSurfaceRadialEnergyDensity e m fermiEnergy energy broadening) =
        ∫ energy in m..energyMax,
          -(e ^ 2 * m / fermiEnergy) *
            (lorentzianSpectralKernel (energy - fermiEnergy) broadening -
              lorentzianSpectralKernel (energy + fermiEnergy) broadening) := by
      apply intervalIntegral.integral_congr
      intro energy _
      exact stredaSurfaceRadialEnergyDensity_eq_lorentzian_difference
        e m fermiEnergy energy broadening hfermi hbroadening
    _ = -(e ^ 2 * m / fermiEnergy) *
        (∫ energy in m..energyMax,
          (lorentzianSpectralKernel (energy - fermiEnergy) broadening -
            lorentzianSpectralKernel (energy + fermiEnergy) broadening)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [intervalIntegral.integral_sub]
      · simpa [sub_neg_eq_add] using hIntMirror
      · exact hIntFermi
      · simpa [sub_neg_eq_add] using hIntMirror

/-- Once the positive-energy interval contains the metallic Fermi energy, the finite Středa
surface energy integral converges to `-(e² m / εF) π`. -/
theorem tendsto_finiteEnergyStredaSurfaceIntegral
    (e m fermiEnergy energyMax : ℝ)
    (hmF : m < fermiEnergy) (hFMax : fermiEnergy < energyMax) :
    Tendsto
      (fun broadening : ℝ =>
        finiteEnergyStredaSurfaceIntegral e m fermiEnergy energyMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(e ^ 2 * m / fermiEnergy) * Real.pi)) := by
  have hfermi : fermiEnergy ≠ 0 := by
    intro hzero
    rw [hzero] at hmF
    linarith
  have hFermiMass :=
    tendsto_integral_lorentzianSpectralKernel_sub_center_of_mem
      fermiEnergy m energyMax hmF hFMax
  have hMirrorMass :=
    tendsto_integral_lorentzianSpectralKernel_sub_center_of_center_lt_lower
      (-fermiEnergy) m energyMax (by linarith) (le_of_lt (lt_trans hmF hFMax))
  have hdiff := hFermiMass.sub hMirrorMass
  have hscale : Tendsto
      (fun _ : ℝ => -(e ^ 2 * m / fermiEnergy))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(e ^ 2 * m / fermiEnergy))) :=
    tendsto_const_nhds
  have hscaled := hscale.mul hdiff
  apply Tendsto.congr' ?_ hscaled
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  rw [finiteEnergyStredaSurfaceIntegral_eq_lorentzian_difference
    e m fermiEnergy energyMax broadening hfermi hbroadening.ne']

end

end AnomalousHall.MassiveDirac
