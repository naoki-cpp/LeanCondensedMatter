import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.BerrySymmetry
import LeanCondensedMatter.Transport.Analysis.BandOccupation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# Intrinsic Berry weight for the metallic massive Dirac cone

For a single continuum Dirac cone, the occupied-state response must keep the ultraviolet regulator
explicit. After angular reduction and the change from radial momentum to the positive Dirac energy
`ε`, the dimensionless Berry-weight density of band sign `s = ±1` is

```text
-s m / (2 ε²).
```

The canonical zero-temperature finite-cutoff response in this file multiplies that density by the
generic strict Fermi occupation evaluated on the actual signed band energy `s ε`, and integrates
both bands over the common positive-energy interval `[m, Λ]`. Under the benchmark convention
`0 < m ≤ εF ≤ Λ`, this occupation-derived response reduces to

* the filled lower-band shell from `m` to `Λ`, and
* the occupied upper-band shell from `m` to `εF`.

The resulting finite-cutoff weight is

```text
m / (2 εF) - m / (2 Λ).
```

The historical `valence` / `conduction` names are retained only as downstream names for these two
shell integrals. No infinite-cutoff limit and no `e²/h` transport prefactor are claimed in this
file.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory Set QuantumTheory.Transport
open scoped Interval

/-- Radially reduced Berry-weight density in positive-energy coordinates.

This is the result of combining `Ω_s(p) = -s m v²/(2E³)` with the radial Jacobian
`p dp = E dE / v²`; hence the velocity cancels before the energy integration. Integer power
`ε⁻²` is used so the finite-shell integral is handled directly by Mathlib's `integral_zpow`. -/
def radialBerryEnergyDensity (band : Band) (m ε : ℝ) : ℝ :=
  -(bandSign band * m / 2) * ε ^ (-2 : ℤ)

/-- Berry weight accumulated over a finite positive-energy shell. -/
def energyShellBerryWeight (band : Band) (m ε₀ ε₁ : ℝ) : ℝ :=
  ∫ ε in ε₀..ε₁, radialBerryEnergyDensity band m ε

/-- Exact finite-shell Berry-weight integral for `0 < ε₀ ≤ ε₁`.

The shell avoids the singularity at zero, so the `zpow` integral at exponent `-2` applies
without introducing a derivative/NormedSpace instance into the model layer. -/
theorem energyShellBerryWeight_eq (band : Band) (m ε₀ ε₁ : ℝ)
    (hε₀ : 0 < ε₀) (hord : ε₀ ≤ ε₁) :
    energyShellBerryWeight band m ε₀ ε₁ =
      (bandSign band * m / 2) * (ε₁⁻¹ - ε₀⁻¹) := by
  have hzero : 0 ∉ uIcc ε₀ ε₁ := by
    rw [uIcc_of_le hord]
    intro h0
    exact (not_le_of_gt hε₀) h0.1
  have hzpow :
      (∫ ε : ℝ in ε₀..ε₁, ε ^ (-2 : ℤ)) =
        (ε₁ ^ ((-2 : ℤ) + 1) - ε₀ ^ ((-2 : ℤ) + 1)) /
          (((-2 : ℤ) : ℝ) + 1) :=
    integral_zpow (Or.inr ⟨by norm_num, hzero⟩)
  unfold energyShellBerryWeight radialBerryEnergyDensity
  rw [intervalIntegral.integral_const_mul, hzpow]
  norm_num
  ring

/-- Zero-temperature occupation-weighted radial Berry density. The occupation is evaluated on the
actual signed band energy `s ε`, while `ε` itself remains the positive energy coordinate used by the
radial reduction. -/
def zeroTemperatureOccupiedRadialBerryEnergyDensity
    (band : Band) (m fermiEnergy ε : ℝ) : ℝ :=
  bandStateOccupation (zeroTemperatureOccupation fermiEnergy)
      (fun band ε => bandSign band * ε) band ε *
    radialBerryEnergyDensity band m ε

/-- Zero-temperature occupied Berry weight of one band inside the common positive-energy cutoff
interval `[m, Λ]`. -/
def zeroTemperatureOccupiedBandBerryWeightCutoff
    (band : Band) (m fermiEnergy Λ : ℝ) : ℝ :=
  ∫ ε in m..Λ,
    zeroTemperatureOccupiedRadialBerryEnergyDensity band m fermiEnergy ε

/-- Canonical zero-temperature occupied-state Berry weight at finite positive-energy cutoff. Both
bands are integrated over the same cutoff interval; the generic spectral occupation selects the
filled lower band and the occupied part of the upper band. -/
def zeroTemperatureOccupiedBerryWeightCutoff
    (m fermiEnergy Λ : ℝ) : ℝ :=
  zeroTemperatureOccupiedBandBerryWeightCutoff .lower m fermiEnergy Λ +
    zeroTemperatureOccupiedBandBerryWeightCutoff .upper m fermiEnergy Λ

/-- In `0 < m ≤ εF ≤ Λ`, zero-temperature occupation leaves the lower-band Berry density unchanged
throughout the finite cutoff interval. -/
theorem zeroTemperatureOccupiedBandBerryWeightCutoff_lower_eq
    (m εF Λ : ℝ) (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    zeroTemperatureOccupiedBandBerryWeightCutoff .lower m εF Λ =
      energyShellBerryWeight .lower m m Λ := by
  have hmΛ : m ≤ Λ := hmF.trans hFΛ
  unfold zeroTemperatureOccupiedBandBerryWeightCutoff energyShellBerryWeight
  apply intervalIntegral.integral_congr
  intro ε hε
  rw [uIcc_of_le hmΛ] at hε
  have hocc :
      bandStateOccupation (zeroTemperatureOccupation εF)
          (fun band ε => bandSign band * ε) .lower ε = 1 := by
    apply bandStateOccupation_zeroTemperature_eq_one_of_lt
    simp only [bandSign]
    linarith [hm, hmF, hε.1]
  simp [zeroTemperatureOccupiedRadialBerryEnergyDensity, hocc]

/-- If `m ≤ εF ≤ Λ`, zero-temperature occupation truncates the upper-band Berry integral at `εF`.
The strict endpoint convention differs only at the singleton `{εF}`, which is invisible to
Lebesgue integration. -/
theorem zeroTemperatureOccupiedBandBerryWeightCutoff_upper_eq
    (m εF Λ : ℝ) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    zeroTemperatureOccupiedBandBerryWeightCutoff .upper m εF Λ =
      energyShellBerryWeight .upper m m εF := by
  unfold zeroTemperatureOccupiedBandBerryWeightCutoff energyShellBerryWeight
  calc
    (∫ ε in m..Λ,
        zeroTemperatureOccupiedRadialBerryEnergyDensity .upper m εF ε) =
        ∫ ε in m..Λ,
          Set.indicator {ε : ℝ | ε ≤ εF}
            (fun ε => radialBerryEnergyDensity .upper m ε) ε := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne εF] with ε hne
      intro _
      unfold zeroTemperatureOccupiedRadialBerryEnergyDensity bandStateOccupation
      simp only [bandSign, one_mul]
      by_cases hlt : ε < εF
      · simp [zeroTemperatureOccupation, hlt, hlt.le]
      · have hgt : εF < ε :=
          lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
        simp [zeroTemperatureOccupation, hlt, not_le.mpr hgt]
    _ = ∫ ε in m..εF, radialBerryEnergyDensity .upper m ε := by
      exact intervalIntegral.integral_indicator ⟨hmF, hFΛ⟩

/-- Filled lower-band Berry weight from the positive gap edge `m` to a finite UV cutoff `Λ`, under
the benchmark convention `m > 0`. This is a downstream shell name, not the source of occupation. -/
def valenceBerryWeightCutoff (m Λ : ℝ) : ℝ :=
  energyShellBerryWeight .lower m m Λ

/-- Occupied upper-band Berry weight from the gap edge `m` to the Fermi energy `εF`. This is a
downstream shell name for the region selected by zero-temperature occupation. -/
def conductionBerryWeight (m εF : ℝ) : ℝ :=
  energyShellBerryWeight .upper m m εF

/-- The occupation-derived finite-cutoff response reduces to the familiar filled-lower plus
occupied-upper shell decomposition. -/
theorem zeroTemperatureOccupiedBerryWeightCutoff_eq_valence_add_conduction
    (m εF Λ : ℝ) (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    zeroTemperatureOccupiedBerryWeightCutoff m εF Λ =
      valenceBerryWeightCutoff m Λ + conductionBerryWeight m εF := by
  unfold zeroTemperatureOccupiedBerryWeightCutoff
  rw [zeroTemperatureOccupiedBandBerryWeightCutoff_lower_eq m εF Λ hm hmF hFΛ,
    zeroTemperatureOccupiedBandBerryWeightCutoff_upper_eq m εF Λ hmF hFΛ]
  rfl

/-- Finite-cutoff lower-band contribution: `1/2 - m/(2Λ)`. -/
theorem valenceBerryWeightCutoff_eq (m Λ : ℝ) (hm : 0 < m) (hmΛ : m ≤ Λ) :
    valenceBerryWeightCutoff m Λ = 1 / 2 - m / (2 * Λ) := by
  rw [valenceBerryWeightCutoff, energyShellBerryWeight_eq .lower m m Λ hm hmΛ]
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hΛ0 : Λ ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hmΛ)
  simp
  field_simp [hm0, hΛ0]
  ring

/-- Occupied upper-band contribution: `m/(2εF) - 1/2`. -/
theorem conductionBerryWeight_eq (m εF : ℝ) (hm : 0 < m) (hmF : m ≤ εF) :
    conductionBerryWeight m εF = m / (2 * εF) - 1 / 2 := by
  rw [conductionBerryWeight, energyShellBerryWeight_eq .upper m m εF hm hmF]
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hF0 : εF ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hmF)
  simp
  field_simp [hm0, hF0]

/-- Total occupied-state Berry weight with a finite lower-band ultraviolet cutoff. This historical
wrapper keeps the established API while the occupation-derived response is the canonical source of
the lower/upper decomposition. -/
def metallicBerryWeightCutoff (m εF Λ : ℝ) : ℝ :=
  valenceBerryWeightCutoff m Λ + conductionBerryWeight m εF

/-- The historical finite-cutoff wrapper agrees with the occupation-derived response in the
positive-mass metallic-or-band-edge regime. -/
theorem metallicBerryWeightCutoff_eq_zeroTemperatureOccupied
    (m εF Λ : ℝ) (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    metallicBerryWeightCutoff m εF Λ =
      zeroTemperatureOccupiedBerryWeightCutoff m εF Λ := by
  rw [zeroTemperatureOccupiedBerryWeightCutoff_eq_valence_add_conduction
    m εF Λ hm hmF hFΛ]
  rfl

/-- The finite-cutoff occupied Berry weight keeps the single-cone regulator term explicit. -/
theorem metallicBerryWeightCutoff_eq (m εF Λ : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    metallicBerryWeightCutoff m εF Λ =
      m / (2 * εF) - m / (2 * Λ) := by
  rw [metallicBerryWeightCutoff,
    valenceBerryWeightCutoff_eq m Λ hm (hmF.trans hFΛ),
    conductionBerryWeight_eq m εF hm hmF]
  ring

/-- The occupation-derived finite-cutoff response has the same closed form as the established
massive-Dirac benchmark. -/
theorem zeroTemperatureOccupiedBerryWeightCutoff_eq
    (m εF Λ : ℝ) (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    zeroTemperatureOccupiedBerryWeightCutoff m εF Λ =
      m / (2 * εF) - m / (2 * Λ) := by
  rw [← metallicBerryWeightCutoff_eq_zeroTemperatureOccupied m εF Λ hm hmF hFΛ]
  exact metallicBerryWeightCutoff_eq m εF Λ hm hmF hFΛ

end

end AnomalousHall.MassiveDirac
