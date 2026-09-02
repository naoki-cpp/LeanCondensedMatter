import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.Response
import Mathlib.Topology.Algebra.Order.Field

set_option linter.style.header false

/-!
# Metallic intrinsic Hall conductivity for the massive Dirac cone

The canonical finite-cutoff Berry weight is the zero-temperature occupation-derived response
proved upstream. In the benchmark regime `|m| ≤ εF ≤ Λ`, including the massless endpoint, it
reduces to

```text
C(εF, Λ) = m / (2 εF) - m / (2 Λ).
```

Here we prove that this cutoff-dependent weight tends to `m / (2 εF)` as `Λ → +∞` and attach the
physical-momentum Berry/Kubo normalization. For

```text
C = (1 / 2π) ∫ d²p Ω(p),
```

the physical-momentum measure `d²p/(2πℏ)²` and the clean Berry-response coefficient `-e²ℏ`
combine to `-e²/h`, with `h = 2πℏ`. The resulting metallic benchmark is

```text
σxy^int = -(e² / 2h) * m / εF.
```

The algebraic normalization identities are stated for the totalized real-field operations; physical
uses may separately impose nonzero `ℏ` and Fermi energy. This file does not identify a finite
regularized Středa calculation with the continuum limit.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Planck's constant expressed through the reduced Planck constant, `h = 2πℏ`. -/
def planckFromReduced (hbar : ℝ) : ℝ :=
  2 * Real.pi * hbar

/-- Metallic occupied-state Berry weight after removing the continuum ultraviolet cutoff. -/
def metallicBerryWeightUV (m εF : ℝ) : ℝ :=
  m / (2 * εF)

/-- The occupation-derived finite-cutoff Berry weight in a form adapted to the `Λ → +∞` proof. -/
private theorem zeroTemperatureOccupiedBerryWeightCutoff_eq_zpow (m εF Λ : ℝ)
    (hmF : |m| ≤ εF) (hFΛ : εF ≤ Λ) :
    zeroTemperatureOccupiedBerryWeightCutoff m εF Λ =
      metallicBerryWeightUV m εF - (m / 2) * Λ ^ (-1 : ℤ) := by
  rw [zeroTemperatureOccupiedBerryWeightCutoff_eq m εF Λ hmF hFΛ]
  simp [metallicBerryWeightUV, div_eq_mul_inv]
  ring

private theorem tendsto_metallicBerryWeightUV_sub_correction_atTop (m εF : ℝ) :
    Tendsto
      (fun Λ : ℝ => metallicBerryWeightUV m εF - (m / 2) * Λ ^ (-1 : ℤ))
      atTop (nhds (metallicBerryWeightUV m εF)) := by
  have hInv : Tendsto (fun Λ : ℝ => Λ ^ (-1 : ℤ)) atTop (nhds 0) :=
    tendsto_zpow_atTop_zero (by norm_num)
  have hCorrection :
      Tendsto (fun Λ : ℝ => (m / 2) * Λ ^ (-1 : ℤ)) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => m / 2) atTop (nhds (m / 2))).mul hInv
  simpa using tendsto_const_nhds.sub hCorrection

/-- The canonical zero-temperature occupation-derived finite-cutoff Berry weight converges to the
metallic continuum weight, including the massless endpoint. -/
theorem tendsto_zeroTemperatureOccupiedBerryWeightCutoff_atTop (m εF : ℝ)
    (hmF : |m| ≤ εF) :
    Tendsto (zeroTemperatureOccupiedBerryWeightCutoff m εF) atTop
      (nhds (metallicBerryWeightUV m εF)) := by
  apply Tendsto.congr' ?_ (tendsto_metallicBerryWeightUV_sub_correction_atTop m εF)
  filter_upwards [eventually_ge_atTop εF] with Λ hFΛ
  exact (zeroTemperatureOccupiedBerryWeightCutoff_eq_zpow m εF Λ hmF hFΛ).symm

/-- Berry/Kubo Hall prefactor written directly in the physical-momentum convention.

The factor `2π` converts the dimensionless Berry weight `C = (1/2π) ∫ d²p Ω` back to the full
momentum integral. -/
def intrinsicHallPrefactorFromMomentumMeasure (e hbar : ℝ) : ℝ :=
  -(e ^ 2) * hbar * (2 * Real.pi) * momentumMeasurePrefactor hbar

/-- The physical-momentum measure normalization reduces the Berry/Kubo prefactor to `-e²/h` as an
identity of totalized real-field expressions. -/
theorem intrinsicHallPrefactorFromMomentumMeasure_eq (e hbar : ℝ) :
    intrinsicHallPrefactorFromMomentumMeasure e hbar =
      -(e ^ 2 / planckFromReduced hbar) := by
  by_cases hhbar : hbar = 0
  · simp [intrinsicHallPrefactorFromMomentumMeasure, momentumMeasurePrefactor,
      planckFromReduced, hhbar]
  · unfold intrinsicHallPrefactorFromMomentumMeasure momentumMeasurePrefactor planckFromReduced
    field_simp [hhbar, Real.pi_ne_zero]

/-- Finite-cutoff intrinsic Hall conductivity obtained from the canonical zero-temperature
occupation-derived Berry weight. -/
def intrinsicHallConductivityCutoff (e hbar m εF Λ : ℝ) : ℝ :=
  intrinsicHallPrefactorFromMomentumMeasure e hbar *
    zeroTemperatureOccupiedBerryWeightCutoff m εF Λ

/-- Clean metallic intrinsic Hall conductivity after the UV cutoff is removed. -/
def intrinsicHallConductivity (e hbar m εF : ℝ) : ℝ :=
  intrinsicHallPrefactorFromMomentumMeasure e hbar * metallicBerryWeightUV m εF

/-- The occupation-derived finite-cutoff Hall conductivity converges to the clean metallic intrinsic
response, including the massless endpoint. -/
theorem tendsto_intrinsicHallConductivityCutoff_atTop (e hbar m εF : ℝ)
    (hmF : |m| ≤ εF) :
    Tendsto (intrinsicHallConductivityCutoff e hbar m εF) atTop
      (nhds (intrinsicHallConductivity e hbar m εF)) := by
  unfold intrinsicHallConductivityCutoff intrinsicHallConductivity
  exact tendsto_const_nhds.mul
    (tendsto_zeroTemperatureOccupiedBerryWeightCutoff_atTop m εF hmF)

/-- Massive-Dirac intrinsic AHE closed form,
`σxy^int = -(e²/2h) (m/εF)`, stated for the totalized real-field operations. -/
theorem intrinsicHallConductivity_eq_massiveDirac (e hbar m εF : ℝ) :
    intrinsicHallConductivity e hbar m εF =
      -(e ^ 2 / (2 * planckFromReduced hbar)) * (m / εF) := by
  rw [intrinsicHallConductivity, intrinsicHallPrefactorFromMomentumMeasure_eq]
  unfold metallicBerryWeightUV
  by_cases hhbar : hbar = 0
  · simp [planckFromReduced, hhbar]
  · by_cases hεF : εF = 0
    · simp [hεF]
    · unfold planckFromReduced
      field_simp [hhbar, hεF, Real.pi_ne_zero]

end

end AnomalousHall.MassiveDirac
