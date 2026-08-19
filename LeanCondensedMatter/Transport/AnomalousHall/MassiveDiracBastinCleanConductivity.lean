import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPairBerry
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsicConductivity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Clean radial integral of the massive-Dirac Bastin pair limit

The preceding Bastin-pair theorem identifies the fixed-momentum, fixed-window zero-broadening
limit with

```text
-2π e² Ω_n(p).
```

This file integrates that already-extracted clean profile over the occupied radial shells used by
the massive-Dirac intrinsic benchmark and restores the canonical Bastin trace prefactor `ℏ/(2π)`,
the angular factor `2π`, and the physical-momentum measure `d²p/(2πℏ)²`.

The resulting finite-cutoff response is exactly the existing
`intrinsicHallConductivityCutoff`, and its ultraviolet limit is therefore the clean metallic
intrinsic Hall conductivity.

Importantly, this is an integral of the *clean limit profile*.  It does not yet prove that a
momentum integral of the finite-broadening Bastin kernel converges to this integral.  That remaining
limit-interchange statement requires a separate uniform/dominated estimate.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Named real clean-limit profile extracted from the opposite-source interband Bastin pair. -/
def cleanInterbandBastinPairLimitDensity
    (band : Band) (e v m px py : ℝ) : ℝ :=
  -2 * Real.pi * (e ^ 2 * berryCurvature band v m px py)

/-- The pointwise fixed-window theorem from the preceding slice, expressed through the named clean
Bastin-pair limit density. -/
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

/-- Occupied clean Bastin-pair radial weight with the same single-cone UV cutoff convention as the
existing intrinsic benchmark: filled lower band from `m` to `Λ`, plus occupied upper band from `m`
to `εF`. -/
def occupiedCleanInterbandBastinPairCutoff
    (e m εF Λ : ℝ) : ℝ :=
  cleanInterbandBastinPairEnergyShellIntegral .lower e m m Λ +
    cleanInterbandBastinPairEnergyShellIntegral .upper e m m εF

/-- The occupied clean Bastin-pair radial weight is `-2π e²` times the finite-cutoff Berry weight. -/
theorem occupiedCleanInterbandBastinPairCutoff_eq
    (e m εF Λ : ℝ) :
    occupiedCleanInterbandBastinPairCutoff e m εF Λ =
      (-2 * Real.pi * e ^ 2) * metallicBerryWeightCutoff m εF Λ := by
  unfold occupiedCleanInterbandBastinPairCutoff metallicBerryWeightCutoff
  rw [cleanInterbandBastinPairEnergyShellIntegral_eq,
    cleanInterbandBastinPairEnergyShellIntegral_eq]
  ring

/-- Scalar prefactor that converts the canonical traced Bastin energy kernel to the static Hall
response before the momentum measure is applied.  Because the current vertices already contain
the charge `-e`, this factor carries no additional charge power. -/
def bastinTraceHallPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Finite-cutoff Hall response obtained by applying the Bastin trace normalization, the angular
integral, and the physical-momentum measure to the occupied clean interband-pair radial weight. -/
def bastinCleanHallConductivityCutoff
    (e hbar m εF Λ : ℝ) : ℝ :=
  bastinTraceHallPrefactor hbar *
    (2 * Real.pi * momentumMeasurePrefactor hbar) *
      occupiedCleanInterbandBastinPairCutoff e m εF Λ

/-- The clean radial Bastin-pair integral has exactly the same finite-cutoff normalization as the
existing occupied-state intrinsic Hall conductivity. -/
theorem bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff
    (e hbar m εF Λ : ℝ) :
    bastinCleanHallConductivityCutoff e hbar m εF Λ =
      intrinsicHallConductivityCutoff e hbar m εF Λ := by
  unfold bastinCleanHallConductivityCutoff
  rw [occupiedCleanInterbandBastinPairCutoff_eq]
  unfold bastinTraceHallPrefactor intrinsicHallConductivityCutoff
    intrinsicHallPrefactorFromMomentumMeasure
  field_simp [Real.pi_ne_zero]
  ring

/-- Removing the finite radial UV cutoff from the integrated clean Bastin-pair profile reproduces
the existing clean metallic intrinsic Hall conductivity.  This uses the already-proved cutoff
limit; it is not a finite-broadening/momentum limit interchange. -/
theorem tendsto_bastinCleanHallConductivityCutoff_atTop
    (e hbar m εF : ℝ) (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (bastinCleanHallConductivityCutoff e hbar m εF) atTop
      (nhds (intrinsicHallConductivity e hbar m εF)) := by
  have hfun :
      bastinCleanHallConductivityCutoff e hbar m εF =
        intrinsicHallConductivityCutoff e hbar m εF := by
    funext Λ
    exact bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff
      e hbar m εF Λ
  rw [hfun]
  exact tendsto_intrinsicHallConductivityCutoff_atTop e hbar m εF hm hmF

/-- Closed metallic benchmark reached by the integrated clean Bastin-pair profile,
`σxy = -(e²/2h) (m/εF)`. -/
theorem tendsto_bastinCleanHallConductivityCutoff_atTop_massiveDirac
    (e hbar m εF : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (bastinCleanHallConductivityCutoff e hbar m εF) atTop
      (nhds (-(e ^ 2 / (2 * planckFromReduced hbar)) * (m / εF))) := by
  rw [← intrinsicHallConductivity_eq_massiveDirac e hbar m εF hhbar
    (lt_of_lt_of_le hm hmF)]
  exact tendsto_bastinCleanHallConductivityCutoff_atTop e hbar m εF hm hmF

end

end AnomalousHall.MassiveDirac
