import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.Response
import Mathlib.Topology.Algebra.Order.Field

set_option linter.style.header false

/-!
# Metallic intrinsic Hall conductivity for the massive Dirac cone

This file closes the clean metallic occupied-state calculation from #1269 without identifying a
finite ultraviolet cutoff with the continuum answer by definition.

The canonical finite-cutoff Berry weight is the zero-temperature occupation-derived response
proved upstream. In the benchmark regime `0 < m ≤ εF ≤ Λ`, it reduces to

```text
C(εF, Λ) = m / (2 εF) - m / (2 Λ).
```

Here we prove that this actual occupation-derived cutoff-dependent weight tends to `m / (2 εF)` as
`Λ → +∞`. We then attach the physical-momentum Berry/Kubo normalization. For

```text
C = (1 / 2π) ∫ d²p Ω(p),
```

the physical-momentum measure `d²p/(2πℏ)²` and the clean Berry-response coefficient `-e²ℏ`
combine to `-e²/h`, with `h = 2πℏ`. The resulting metallic benchmark is

```text
σxy^int = -(e² / 2h) * m / εF.
```

The later Kubo/Bastin/Středa specialization must prove that its response kernel realizes this
Berry normalization; this file does not identify a finite regularized Středa calculation with the
continuum limit.
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

/-- The historical shell-based finite-cutoff wrapper in a form adapted to the `Λ → +∞` proof. -/
theorem metallicBerryWeightCutoff_eq_zpow (m εF Λ : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    metallicBerryWeightCutoff m εF Λ =
      metallicBerryWeightUV m εF - (m / 2) * Λ ^ (-1 : ℤ) := by
  rw [metallicBerryWeightCutoff_eq m εF Λ hm hmF hFΛ]
  simp [metallicBerryWeightUV, div_eq_mul_inv]
  ring

/-- The occupation-derived finite-cutoff Berry weight in a form adapted to the `Λ → +∞` proof. -/
theorem zeroTemperatureOccupiedBerryWeightCutoff_eq_zpow (m εF Λ : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    zeroTemperatureOccupiedBerryWeightCutoff m εF Λ =
      metallicBerryWeightUV m εF - (m / 2) * Λ ^ (-1 : ℤ) := by
  rw [zeroTemperatureOccupiedBerryWeightCutoff_eq m εF Λ hm hmF hFΛ]
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

/-- The historical shell-based finite-cutoff Berry weight converges to the metallic continuum
weight. The equality to the closed finite-cutoff formula is needed only eventually at `+∞`. -/
theorem tendsto_metallicBerryWeightCutoff_atTop (m εF : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (metallicBerryWeightCutoff m εF) atTop
      (nhds (metallicBerryWeightUV m εF)) := by
  apply Tendsto.congr' ?_ (tendsto_metallicBerryWeightUV_sub_correction_atTop m εF)
  filter_upwards [eventually_ge_atTop εF] with Λ hFΛ
  exact (metallicBerryWeightCutoff_eq_zpow m εF Λ hm hmF hFΛ).symm

/-- The canonical zero-temperature occupation-derived finite-cutoff Berry weight converges to the
metallic continuum weight. -/
theorem tendsto_zeroTemperatureOccupiedBerryWeightCutoff_atTop (m εF : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (zeroTemperatureOccupiedBerryWeightCutoff m εF) atTop
      (nhds (metallicBerryWeightUV m εF)) := by
  apply Tendsto.congr' ?_ (tendsto_metallicBerryWeightUV_sub_correction_atTop m εF)
  filter_upwards [eventually_ge_atTop εF] with Λ hFΛ
  exact (zeroTemperatureOccupiedBerryWeightCutoff_eq_zpow m εF Λ hm hmF hFΛ).symm

/-- Berry/Kubo Hall prefactor written directly in the physical-momentum convention.

The factor `2π` converts the dimensionless Berry weight `C = (1/2π) ∫ d²p Ω` back to the full
momentum integral. -/
def intrinsicHallPrefactorFromMomentumMeasure (e hbar : ℝ) : ℝ :=
  -(e ^ 2) * hbar * (2 * Real.pi) * momentumMeasurePrefactor hbar

/-- The physical-momentum measure normalization reduces the Berry/Kubo prefactor to `-e²/h`. -/
theorem intrinsicHallPrefactorFromMomentumMeasure_eq (e hbar : ℝ) (hhbar : hbar ≠ 0) :
    intrinsicHallPrefactorFromMomentumMeasure e hbar =
      -(e ^ 2 / planckFromReduced hbar) := by
  unfold intrinsicHallPrefactorFromMomentumMeasure momentumMeasurePrefactor planckFromReduced
  field_simp [hhbar, Real.pi_ne_zero]

/-- Finite-cutoff intrinsic Hall conductivity obtained from the canonical zero-temperature
occupation-derived Berry weight. -/
def intrinsicHallConductivityCutoff (e hbar m εF Λ : ℝ) : ℝ :=
  intrinsicHallPrefactorFromMomentumMeasure e hbar *
    zeroTemperatureOccupiedBerryWeightCutoff m εF Λ

/-- In the benchmark regime, the canonical occupation-derived conductivity agrees with the
historical shell-based finite-cutoff wrapper. -/
theorem intrinsicHallConductivityCutoff_eq_shellBased
    (e hbar m εF Λ : ℝ) (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    intrinsicHallConductivityCutoff e hbar m εF Λ =
      intrinsicHallPrefactorFromMomentumMeasure e hbar * metallicBerryWeightCutoff m εF Λ := by
  unfold intrinsicHallConductivityCutoff
  rw [← metallicBerryWeightCutoff_eq_zeroTemperatureOccupied m εF Λ hm hmF hFΛ]

/-- Clean metallic intrinsic Hall conductivity after the UV cutoff is removed. -/
def intrinsicHallConductivity (e hbar m εF : ℝ) : ℝ :=
  intrinsicHallPrefactorFromMomentumMeasure e hbar * metallicBerryWeightUV m εF

/-- The occupation-derived finite-cutoff Hall conductivity converges to the clean metallic intrinsic
response. -/
theorem tendsto_intrinsicHallConductivityCutoff_atTop (e hbar m εF : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (intrinsicHallConductivityCutoff e hbar m εF) atTop
      (nhds (intrinsicHallConductivity e hbar m εF)) := by
  unfold intrinsicHallConductivityCutoff intrinsicHallConductivity
  exact tendsto_const_nhds.mul
    (tendsto_zeroTemperatureOccupiedBerryWeightCutoff_atTop m εF hm hmF)

/-- Metallic massive-Dirac intrinsic AHE benchmark,
`σxy^int = -(e²/2h) (m/εF)`, for positive `ℏ` and Fermi energy. -/
theorem intrinsicHallConductivity_eq_massiveDirac (e hbar m εF : ℝ)
    (hhbar : 0 < hbar) (hεF : 0 < εF) :
    intrinsicHallConductivity e hbar m εF =
      -(e ^ 2 / (2 * planckFromReduced hbar)) * (m / εF) := by
  rw [intrinsicHallConductivity, intrinsicHallPrefactorFromMomentumMeasure_eq e hbar
    (ne_of_gt hhbar)]
  unfold metallicBerryWeightUV
  field_simp [ne_of_gt hhbar, Real.pi_ne_zero, ne_of_gt hεF]

end

end AnomalousHall.MassiveDirac
