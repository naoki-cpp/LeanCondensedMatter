import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePoleExtraction
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Physical pointwise limits of the zero-temperature weighted interband Bastin pair

The preceding extraction theorem keeps the zero-temperature pole weight in its unified scalar form.
This file takes the real part and identifies the three physically distinct cases explicitly:

- a pole below the Fermi energy carries the full clean Berry-curvature weight;
- a pole above the Fermi energy contributes zero;
- a pole exactly at the Fermi surface carries one half of the clean weight.

The exact half-weight is retained pointwise. A later radial integration theorem may discard the
single Fermi-radius set only through an explicit almost-everywhere argument. The radial
dominated-convergence step is deliberately kept downstream of this pointwise layer.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Unified real-part limit of the zero-temperature occupation-weighted interband pair. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-2 * zeroTemperatureLorentzianPoleWeight
        fermiEnergy (bandEnergy band v m px py) *
          (e ^ 2 * berryCurvature band v m px py))) := by
  have hpair := tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral
    band e v m px py fermiEnergy radius hE hradiusPos hradius
  have hre :
      Tendsto
        (fun broadening : ℝ =>
          (targetCenteredZeroTemperatureInterbandBastinPairIntegral
            band e v m px py fermiEnergy radius broadening).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((-2 * Complex.I) *
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
        -2 * zeroTemperatureLorentzianPoleWeight
          fermiEnergy (bandEnergy band v m px py) *
            (e ^ 2 * berryCurvature band v m px py) := by
    rw [Complex.mul_re]
    simp [targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
      band e v m px py hE]
    ring
  rw [hlimit] at hre
  exact hre

/-- A target pole strictly below the Fermi level carries the full clean interband-pair density. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re_of_occupied
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hocc : bandEnergy band v m px py < fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (cleanInterbandBastinPairLimitDensity band e v m px py)) := by
  simpa [zeroTemperatureLorentzianPoleWeight, hocc,
    cleanInterbandBastinPairLimitDensity] using
    tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re
      band e v m px py fermiEnergy radius hE hradiusPos hradius

/-- A target pole strictly above the Fermi level has zero zero-temperature weight. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re_of_unoccupied
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hunocc : fermiEnergy < bandEnergy band v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hnotOcc : ¬ bandEnergy band v m px py < fermiEnergy := not_lt_of_ge hunocc.le
  simpa [zeroTemperatureLorentzianPoleWeight, hnotOcc, hunocc] using
    tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re
      band e v m px py fermiEnergy radius hE hradiusPos hradius

/-- Exactly at the Fermi surface the pointwise zero-temperature pole carries one half of the clean
interband-pair density. -/
theorem tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re_of_fermiSurface
    (band : Band) (e v m px py fermiEnergy radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hfermi : bandEnergy band v m px py = fermiEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m px py fermiEnergy radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) *
        cleanInterbandBastinPairLimitDensity band e v m px py)) := by
  have hnotOcc : ¬ bandEnergy band v m px py < fermiEnergy := by
    simp [hfermi]
  have hnotUnocc : ¬ fermiEnergy < bandEnergy band v m px py := by
    simp [hfermi]
  have h := tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re
    band e v m px py fermiEnergy radius hE hradiusPos hradius
  have hweight :
      zeroTemperatureLorentzianPoleWeight
          fermiEnergy (bandEnergy band v m px py) = Real.pi / 2 := by
    simp [zeroTemperatureLorentzianPoleWeight, hnotOcc, hnotUnocc]
  have htarget :
      -2 * (Real.pi / 2) * (e ^ 2 * berryCurvature band v m px py) =
        (1 / 2 : ℝ) * cleanInterbandBastinPairLimitDensity band e v m px py := by
    unfold cleanInterbandBastinPairLimitDensity
    ring
  rw [hweight, htarget] at h
  exact h

end

end AnomalousHall.MassiveDirac
