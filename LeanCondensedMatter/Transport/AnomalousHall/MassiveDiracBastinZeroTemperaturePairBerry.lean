import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePoleExtraction
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPairBerry
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Berry-curvature form of the zero-temperature weighted Bastin pair

The zero-temperature occupation-weighted fixed-window pair has already been reduced to the scalar
Lorentzian pole weight multiplying the regular spectator/current factor.  This file takes the real
part and identifies that regular factor with Berry curvature.

The resulting pointwise profile keeps the three scalar pole weights explicit:

```text
occupied       : -2π e² Ω_n(p)
unoccupied     : 0
Fermi surface  : -π e² Ω_n(p)
```

No momentum integration or limit/integral interchange is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Named zero-temperature clean limit profile for one target interband Bastin pair.  The scalar
pole weight is `π`, `0`, or `π/2` depending on whether the target-band pole is occupied,
unoccupied, or exactly on the Fermi surface. -/
def zeroTemperatureInterbandBastinPairLimitDensity
    (band : Band) (e v m px py fermiEnergy : ℝ) : ℝ :=
  -2 * zeroTemperatureLorentzianPoleWeight
      fermiEnergy (bandEnergy band v m px py) *
    (e ^ 2 * berryCurvature band v m px py)

/-- The real part of the zero-temperature occupation-weighted interband Bastin pair converges
pointwise to the Berry-curvature profile with the exact zero-temperature pole weight. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re_berryCurvature
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroTemperatureInterbandBastinPairLimitDensity
        band e v m px py fermiEnergy)) := by
  have hpair :=
    tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral
      band e v m px py fermiEnergy radius hE hradiusPos hradius
  have hre :
      Tendsto
        (fun broadening : ℝ =>
          (targetCenteredZeroTemperatureInterbandBastinPairIntegral
            band e v m px py fermiEnergy radius broadening).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((-2 * Complex.I) *
            (zeroTemperatureLorentzianPoleWeight
                fermiEnergy (bandEnergy band v m px py) •
              targetCenteredInterbandSpectatorCurrentFactor
                band e v m px py (0, 0))).re)) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hpair
  have hlimit :
      (((-2 * Complex.I) *
        (zeroTemperatureLorentzianPoleWeight
            fermiEnergy (bandEnergy band v m px py) •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0))).re) =
        zeroTemperatureInterbandBastinPairLimitDensity
          band e v m px py fermiEnergy := by
    rw [Complex.mul_re]
    simp [targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
      band e v m px py hE, zeroTemperatureInterbandBastinPairLimitDensity]
    ring
  rw [hlimit] at hre
  exact hre

/-- An occupied target-band pole reproduces the ordinary clean interband Bastin-pair profile. -/
theorem zeroTemperatureInterbandBastinPairLimitDensity_of_occupied
    (band : Band) (e v m px py fermiEnergy : ℝ)
    (hoccupied : bandEnergy band v m px py < fermiEnergy) :
    zeroTemperatureInterbandBastinPairLimitDensity band e v m px py fermiEnergy =
      cleanInterbandBastinPairLimitDensity band e v m px py := by
  simp [zeroTemperatureInterbandBastinPairLimitDensity,
    cleanInterbandBastinPairLimitDensity, hoccupied]

/-- An unoccupied target-band pole contributes no zero-temperature clean pair weight. -/
theorem zeroTemperatureInterbandBastinPairLimitDensity_of_unoccupied
    (band : Band) (e v m px py fermiEnergy : ℝ)
    (hunoccupied : fermiEnergy < bandEnergy band v m px py) :
    zeroTemperatureInterbandBastinPairLimitDensity band e v m px py fermiEnergy = 0 := by
  simp [zeroTemperatureInterbandBastinPairLimitDensity, hunoccupied]

/-- A target-band pole exactly on the Fermi surface carries half of the ordinary clean pair weight.
-/
theorem zeroTemperatureInterbandBastinPairLimitDensity_at_fermi_surface
    (band : Band) (e v m px py fermiEnergy : ℝ)
    (hfermi : bandEnergy band v m px py = fermiEnergy) :
    zeroTemperatureInterbandBastinPairLimitDensity band e v m px py fermiEnergy =
      (1 / 2 : ℝ) * cleanInterbandBastinPairLimitDensity band e v m px py := by
  unfold zeroTemperatureInterbandBastinPairLimitDensity
  rw [hfermi, zeroTemperatureLorentzianPoleWeight_at_fermi_surface]
  unfold cleanInterbandBastinPairLimitDensity
  ring

end

end AnomalousHall.MassiveDirac
