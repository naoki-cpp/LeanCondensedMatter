import LeanCondensedMatter.Models.MassiveDirac.Model.Berry.Occupation
import LeanCondensedMatter.Models.MassiveDirac.ManyBody.PointwiseHall
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Clean radial integral of the massive-Dirac Bastin pair limit

The preceding Bastin-pair theorem identifies the fixed-momentum, fixed-window zero-broadening
limit with

```text
-2π e² Ω_n(p).
```

This file owns that clean limit profile and its finite radial-energy integrals. The generic
zero-temperature spectral occupation is applied directly to the clean Bastin profile, but no
physical Hall-conductivity normalization is attached here.

Physical normalization by the Bastin trace prefactor, angular integral, and continuum momentum
measure belongs downstream under `MassiveDirac/Conductivity/Hall`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- Named real clean-limit profile extracted from the opposite-source interband Bastin pair. -/
def cleanInterbandBastinPairLimitDensity
    (band : Band) (e v m px py : ℝ) : ℝ :=
  2 * Real.pi * cleanBandFockHallDensity band e v m px py

/-- The full-Fock clean Hall density reproduces the local Bastin pole coefficient. -/
theorem cleanInterbandBastinPairLimitDensity_eq
    (band : Band) (e v m px py : ℝ) :
    cleanInterbandBastinPairLimitDensity band e v m px py =
      -2 * Real.pi * (e ^ 2 * berryCurvature band v m px py) := by
  rw [cleanInterbandBastinPairLimitDensity,
    cleanBandFockHallDensity_eq_neg_chargeSq_berryCurvature]
  ring

/-- Filling the two Fock modes below the Fermi energy gives the occupation-weighted clean
Bastin density used by the existing momentum integrals. The occupied configuration is one
normalized many-body state, including the vacuum and doubly occupied cases. -/
theorem tendsto_zeroTemperaturePointwiseFockHallResponse_re
    (e v m px py fermiEnergy hbar : ℝ) (hhbar : 0 < hbar)
    (hE : energy v m px py ≠ 0) :
    Filter.Tendsto (fun eta => (2 * Real.pi / hbar) *
      (pointwiseFockHallResponse
        (Finset.univ.filter (fun band => bandEnergy band v m px py < fermiEnergy))
        e v m px py hbar hhbar eta hE).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ band : Band, zeroTemperatureOccupation fermiEnergy (bandEnergy band v m px py) *
        cleanInterbandBastinPairLimitDensity band e v m px py)) := by
  classical
  have h := tendsto_pointwiseFockHallResponse_re
    (Finset.univ.filter (fun band => bandEnergy band v m px py < fermiEnergy))
    e v m px py hbar hhbar hE
  have hscaled := (tendsto_const_nhds (x := 2 * Real.pi / hbar)).mul h
  have hcancel : (2 * Real.pi / hbar) * hbar = 2 * Real.pi := by
    field_simp [hhbar.ne']
  simp only [← mul_assoc, hcancel] at hscaled
  simpa [Finset.sum_filter, Finset.mul_sum, zeroTemperatureOccupation,
    cleanInterbandBastinPairLimitDensity, mul_assoc] using hscaled

/-- Radial positive-energy-coordinate density obtained from the clean local Bastin-pair profile.
The Berry part is exactly `radialBerryEnergyDensity`; the factor `-2π e²` is the local pair limit
proved upstream. -/
def cleanInterbandBastinPairRadialEnergyDensity
    (band : Band) (e m energy : ℝ) : ℝ :=
  (-2 * Real.pi * e ^ 2) * radialBerryEnergyDensity band m energy

/-- Clean interband Bastin-pair weight accumulated over one finite radial energy shell. -/
def cleanInterbandBastinPairEnergyShellIntegral
    (band : Band) (e m energy₀ energy₁ : ℝ) : ℝ :=
  ∫ energy in energy₀..energy₁,
    cleanInterbandBastinPairRadialEnergyDensity band e m energy

/-- Radial integration of the clean pair profile factors into `-2π e²` times the corresponding
Berry shell weight. -/
theorem cleanInterbandBastinPairEnergyShellIntegral_eq
    (band : Band) (e m energy₀ energy₁ : ℝ) :
    cleanInterbandBastinPairEnergyShellIntegral band e m energy₀ energy₁ =
      (-2 * Real.pi * e ^ 2) * energyShellBerryWeight band m energy₀ energy₁ := by
  unfold cleanInterbandBastinPairEnergyShellIntegral
    cleanInterbandBastinPairRadialEnergyDensity energyShellBerryWeight
  rw [intervalIntegral.integral_const_mul]

/-- Zero-temperature occupation-weighted radial clean Bastin-pair density. The generic spectral
occupation acts directly on the clean Bastin profile at the signed band energy. -/
def zeroTemperatureOccupiedCleanInterbandBastinPairRadialEnergyDensity
    (band : Band) (e m fermiEnergy energy : ℝ) : ℝ :=
  bandStateOccupation (zeroTemperatureOccupation fermiEnergy)
      (fun band energy => bandSign band * energy) band energy *
    cleanInterbandBastinPairRadialEnergyDensity band e m energy

/-- The occupation-weighted clean Bastin density is `-2π e²` times the corresponding
occupation-weighted Berry density. -/
theorem zeroTemperatureOccupiedCleanInterbandBastinPairRadialEnergyDensity_eq
    (band : Band) (e m fermiEnergy energy : ℝ) :
    zeroTemperatureOccupiedCleanInterbandBastinPairRadialEnergyDensity
        band e m fermiEnergy energy =
      (-2 * Real.pi * e ^ 2) *
        zeroTemperatureOccupiedRadialBerryEnergyDensity band m fermiEnergy energy := by
  unfold zeroTemperatureOccupiedCleanInterbandBastinPairRadialEnergyDensity
    cleanInterbandBastinPairRadialEnergyDensity
    zeroTemperatureOccupiedRadialBerryEnergyDensity
  ring

/-- Occupied clean Bastin-pair weight of one band inside the common positive-energy cutoff interval
`[|m|, Λ]`. -/
def zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff
    (band : Band) (e m fermiEnergy Λ : ℝ) : ℝ :=
  ∫ energy in |m|..Λ,
    zeroTemperatureOccupiedCleanInterbandBastinPairRadialEnergyDensity
      band e m fermiEnergy energy

/-- The occupation-weighted clean Bastin-pair integral of one band factors into `-2π e²` times the
canonical occupation-weighted Berry integral. -/
theorem zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff_eq
    (band : Band) (e m fermiEnergy Λ : ℝ) :
    zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff band e m fermiEnergy Λ =
      (-2 * Real.pi * e ^ 2) *
        zeroTemperatureOccupiedBandBerryWeightCutoff band m fermiEnergy Λ := by
  unfold zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff
    zeroTemperatureOccupiedBandBerryWeightCutoff
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro energy _
  exact zeroTemperatureOccupiedCleanInterbandBastinPairRadialEnergyDensity_eq
    band e m fermiEnergy energy

/-- Canonical zero-temperature occupied clean Bastin-pair radial weight at finite cutoff. Both
bands use the same cutoff interval and occupation selects their contributing states. -/
def zeroTemperatureOccupiedCleanInterbandBastinPairCutoff
    (e m fermiEnergy Λ : ℝ) : ℝ :=
  ∑ band : Band,
    zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff band e m fermiEnergy Λ

/-- The canonical occupied clean Bastin-pair radial weight is `-2π e²` times the canonical
occupation-derived finite-cutoff Berry weight. -/
theorem zeroTemperatureOccupiedCleanInterbandBastinPairCutoff_eq
    (e m fermiEnergy Λ : ℝ) :
    zeroTemperatureOccupiedCleanInterbandBastinPairCutoff e m fermiEnergy Λ =
      (-2 * Real.pi * e ^ 2) *
        zeroTemperatureOccupiedBerryWeightCutoff m fermiEnergy Λ := by
  unfold zeroTemperatureOccupiedCleanInterbandBastinPairCutoff
    zeroTemperatureOccupiedBerryWeightCutoff
  rw [sum_band, sum_band,
    zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff_eq,
    zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff_eq]
  ring

end

end QuantumTheory.Models.MassiveDirac
