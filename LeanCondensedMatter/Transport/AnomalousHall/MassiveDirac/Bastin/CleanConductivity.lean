import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PairBerry
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.Conductivity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Clean radial integral of the massive-Dirac Bastin pair limit

The preceding Bastin-pair theorem identifies the fixed-momentum, fixed-window zero-broadening
limit with

```text
-2π e² Ω_n(p).
```

This file integrates that already-extracted clean profile with the same generic zero-temperature
spectral occupation used by the intrinsic benchmark. Both bands share the finite positive-energy
interval `[m, Λ]`; occupation selects the filled lower band and the occupied part of the upper band.

The canonical finite-cutoff response restores the Bastin trace prefactor `ℏ/(2π)`, the angular
factor `2π`, and the physical-momentum measure `d²p/(2πℏ)²`. It is exactly the occupation-derived
`intrinsicHallConductivityCutoff`, and its ultraviolet limit is therefore the clean metallic
intrinsic Hall conductivity.

Importantly, this is an integral of the *clean limit profile*. It does not yet prove that a momentum
integral of the finite-broadening Bastin kernel converges to this integral. That remaining
limit-interchange statement requires a separate uniform/dominated estimate.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Named real clean-limit profile extracted from the opposite-source interband Bastin pair. -/
def cleanInterbandBastinPairLimitDensity
    (band : Band) (e v m px py : ℝ) : ℝ :=
  -2 * Real.pi * (e ^ 2 * berryCurvature band v m px py)

/-- The pointwise fixed-window theorem expressed through the named clean Bastin-pair limit density. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_cleanLimitDensity
    (band : Band) (e v m px py radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          band e v m px py radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (cleanInterbandBastinPairLimitDensity band e v m px py)) := by
  simpa [cleanInterbandBastinPairLimitDensity] using
    tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
      band e v m px py radius hE hradiusPos hradius

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
`[m, Λ]`. -/
def zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff
    (band : Band) (e m fermiEnergy Λ : ℝ) : ℝ :=
  ∫ energy in m..Λ,
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
  zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff .lower e m fermiEnergy Λ +
    zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff .upper e m fermiEnergy Λ

/-- The canonical occupied clean Bastin-pair radial weight is `-2π e²` times the canonical
occupation-derived finite-cutoff Berry weight. -/
theorem zeroTemperatureOccupiedCleanInterbandBastinPairCutoff_eq
    (e m fermiEnergy Λ : ℝ) :
    zeroTemperatureOccupiedCleanInterbandBastinPairCutoff e m fermiEnergy Λ =
      (-2 * Real.pi * e ^ 2) *
        zeroTemperatureOccupiedBerryWeightCutoff m fermiEnergy Λ := by
  unfold zeroTemperatureOccupiedCleanInterbandBastinPairCutoff
    zeroTemperatureOccupiedBerryWeightCutoff
  rw [zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff_eq,
    zeroTemperatureOccupiedCleanInterbandBastinPairBandCutoff_eq]
  ring

/-- Scalar prefactor that converts the canonical traced Bastin energy kernel to the static Hall
response before the momentum measure is applied. Because the current vertices already contain the
charge `-e`, this factor carries no additional charge power. -/
def bastinTraceHallPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Finite-cutoff Hall response obtained from the canonical occupation-weighted clean Bastin-pair
radial integral, the Bastin trace normalization, the angular integral, and the physical-momentum
measure. -/
def bastinCleanHallConductivityCutoff
    (e hbar m εF Λ : ℝ) : ℝ :=
  bastinTraceHallPrefactor hbar *
    (2 * Real.pi * momentumMeasurePrefactor hbar) *
      zeroTemperatureOccupiedCleanInterbandBastinPairCutoff e m εF Λ

/-- The canonical clean radial Bastin-pair integral has exactly the same finite-cutoff normalization
as the canonical occupation-derived intrinsic Hall conductivity. -/
theorem bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff
    (e hbar m εF Λ : ℝ) :
    bastinCleanHallConductivityCutoff e hbar m εF Λ =
      intrinsicHallConductivityCutoff e hbar m εF Λ := by
  unfold bastinCleanHallConductivityCutoff
  rw [zeroTemperatureOccupiedCleanInterbandBastinPairCutoff_eq]
  unfold bastinTraceHallPrefactor intrinsicHallConductivityCutoff
    intrinsicHallPrefactorFromMomentumMeasure
  field_simp [Real.pi_ne_zero]

/-- Removing the finite radial UV cutoff from the integrated occupation-weighted clean Bastin-pair
profile reproduces the clean metallic intrinsic Hall conductivity. This uses the already-proved
cutoff limit; it is not a finite-broadening/momentum limit interchange. -/
theorem tendsto_bastinCleanHallConductivityCutoff_atTop
    (e hbar m εF : ℝ) (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (bastinCleanHallConductivityCutoff e hbar m εF) atTop
      (nhds (intrinsicHallConductivity e hbar m εF)) := by
  refine (tendsto_intrinsicHallConductivityCutoff_atTop e hbar m εF hm hmF).congr' ?_
  filter_upwards with Λ
  exact (bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff
    e hbar m εF Λ).symm

/-- Closed metallic benchmark reached by the integrated clean Bastin-pair profile,
`σxy = -(e²/2h) (m/εF)`. -/
theorem tendsto_bastinCleanHallConductivityCutoff_atTop_massiveDirac
    (e hbar m εF : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (bastinCleanHallConductivityCutoff e hbar m εF) atTop
      (nhds (-(e ^ 2 / (2 * planckFromReduced hbar)) * (m / εF))) := by
  rw [← intrinsicHallConductivity_eq_massiveDirac e hbar m εF hhbar.ne'
    (lt_of_lt_of_le hm hmF).ne']
  exact tendsto_bastinCleanHallConductivityCutoff_atTop e hbar m εF hm hmF

end

end AnomalousHall.MassiveDirac
