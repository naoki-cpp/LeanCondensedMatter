import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePair
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature Lorentzian pole weight in target-centered coordinates

The existing zero-temperature pole theorem is written in the physical energy variable.  The
occupation-weighted interband pair introduced downstream is written instead in the target-centered
offset variable.  This file records the exact translation between the two conventions and carries
the unified occupied/unoccupied/Fermi-surface weight `π / 0 / π/2` into offset coordinates.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Zero-temperature Lorentzian mass in target-centered offset coordinates. -/
noncomputable def targetCenteredZeroTemperatureLorentzianMass
    (center fermiEnergy radius broadening : ℝ) : ℝ :=
  ∫ offset in -radius..radius,
    zeroTemperatureOccupation fermiEnergy (center + offset) *
      lorentzianSpectralKernel offset broadening

/-- Translating the target-centered offset by the pole center reproduces the existing physical
energy-coordinate zero-temperature Lorentzian integral exactly. -/
theorem targetCenteredZeroTemperatureLorentzianMass_eq_energyIntegral
    (center fermiEnergy radius broadening : ℝ) :
    targetCenteredZeroTemperatureLorentzianMass center fermiEnergy radius broadening =
      ∫ energy in center - radius..center + radius,
        zeroTemperatureOccupation fermiEnergy energy *
          lorentzianSpectralKernel (energy - center) broadening := by
  let f : ℝ → ℝ := fun offset =>
    zeroTemperatureOccupation fermiEnergy (center + offset) *
      lorentzianSpectralKernel offset broadening
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := center - radius) (b := center + radius) f center
  have hleft : center - radius - center = -radius := by ring
  have hright : center + radius - center = radius := by ring
  rw [hleft, hright] at hshift
  unfold targetCenteredZeroTemperatureLorentzianMass
  rw [← hshift]
  apply intervalIntegral.integral_congr
  intro energy _
  dsimp [f]
  congr 2
  ring

/-- The target-centered zero-temperature Lorentzian mass converges to the unified pole weight:
`π` below the Fermi level, `0` above it, and `π/2` exactly at the Fermi surface. -/
theorem tendsto_targetCenteredZeroTemperatureLorentzianMass
    (center fermiEnergy radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureLorentzianMass
          center fermiEnergy radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroTemperatureLorentzianPoleWeight fermiEnergy center)) := by
  have h := tendsto_zeroTemperatureOccupation_lorentzian_finite_window
    center fermiEnergy radius hradius
  have hfun :
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureLorentzianMass
          center fermiEnergy radius broadening) =
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          zeroTemperatureOccupation fermiEnergy energy *
            lorentzianSpectralKernel (energy - center) broadening) := by
    funext broadening
    exact targetCenteredZeroTemperatureLorentzianMass_eq_energyIntegral
      center fermiEnergy radius broadening
  rw [hfun]
  exact h

/-- Band-energy specialization of the unified target-centered zero-temperature pole weight. -/
theorem tendsto_targetCenteredZeroTemperatureLorentzianMass_band
    (band : Band) (v m px py fermiEnergy radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredZeroTemperatureLorentzianMass
          (bandEnergy band v m px py) fermiEnergy radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroTemperatureLorentzianPoleWeight
        fermiEnergy (bandEnergy band v m px py))) := by
  exact tendsto_targetCenteredZeroTemperatureLorentzianMass
    (bandEnergy band v m px py) fermiEnergy radius hradius

end

end AnomalousHall.MassiveDirac
