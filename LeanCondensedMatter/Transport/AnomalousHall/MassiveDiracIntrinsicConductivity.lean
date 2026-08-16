import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsic
import Mathlib.Topology.Algebra.Order.Field

set_option linter.style.header false

/-!
# Metallic intrinsic Hall conductivity for the massive Dirac cone

This file closes the clean metallic occupied-state calculation from #1269 without identifying a
finite ultraviolet cutoff with the continuum answer by definition.

The finite-cutoff Berry weight proved upstream is

```text
C(εF, Λ) = m / (2 εF) - m / (2 Λ).
```

Here we prove that the actual cutoff-dependent weight tends to `m / (2 εF)` as `Λ → +∞`.  We then
attach the physical-momentum Berry/Kubo normalization.  For

```text
C = (1 / 2π) ∫ d²p Ω(p),
```

the physical-momentum measure `d²p/(2πℏ)²` and the clean Berry-response coefficient `-e²ℏ`
combine to `-e²/h`, with `h = 2πℏ`.  The resulting metallic benchmark is

```text
σxy^int = -(e² / 2h) * m / εF.
```

The later Kubo/Bastin/Středa specialization must prove that its response kernel realizes this
Berry normalization; this file does not identify a finite regularized Středa calculation with the
continuum limit.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Planck's constant expressed through the reduced Planck constant, `h = 2πℏ`. -/
def planckFromReduced (hbar : ℝ) : ℝ :=
  2 * Real.pi * hbar

/-- Metallic occupied-state Berry weight after removing the continuum ultraviolet cutoff. -/
def metallicBerryWeightUV (m εF : ℝ) : ℝ :=
  m / (2 * εF)

/-- The finite-cutoff formula in a form adapted to the `Λ → +∞` proof. -/
theorem metallicBerryWeightCutoff_eq_zpow (m εF Λ : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    metallicBerryWeightCutoff m εF Λ =
      metallicBerryWeightUV m εF - (m / 2) * Λ ^ (-1 : ℤ) := by
  rw [metallicBerryWeightCutoff_eq m εF Λ hm hmF hFΛ]
  simp [metallicBerryWeightUV, div_eq_mul_inv]
  ring

/-- The actual finite-cutoff occupied-state Berry weight converges to the metallic continuum
weight.  The equality to the closed finite-cutoff formula is needed only eventually at `+∞`. -/
theorem tendsto_metallicBerryWeightCutoff_atTop (m εF : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (metallicBerryWeightCutoff m εF) atTop
      (𝓝 (metallicBerryWeightUV m εF)) := by
  have hInv : Tendsto (fun Λ : ℝ => Λ ^ (-1 : ℤ)) atTop (𝓝 0) :=
    tendsto_zpow_atTop_zero (by norm_num)
  have hConst : Tendsto (fun _ : ℝ => m / 2) atTop (𝓝 (m / 2)) :=
    tendsto_const_nhds
  have hCorrection :
      Tendsto (fun Λ : ℝ => (m / 2) * Λ ^ (-1 : ℤ)) atTop (𝓝 0) := by
    simpa using hConst.mul hInv
  have hClosed :
      Tendsto
        (fun Λ : ℝ => metallicBerryWeightUV m εF - (m / 2) * Λ ^ (-1 : ℤ))
        atTop (𝓝 (metallicBerryWeightUV m εF)) := by
    simpa using (tendsto_const_nhds.sub hCorrection)
  apply Tendsto.congr' ?_ hClosed
  filter_upwards [eventually_ge_atTop εF] with Λ hFΛ
  exact metallicBerryWeightCutoff_eq_zpow m εF Λ hm hmF hFΛ

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
  ring

/-- Finite-cutoff intrinsic Hall conductivity before removing the single-cone UV regulator. -/
def intrinsicHallConductivityCutoff (e hbar m εF Λ : ℝ) : ℝ :=
  intrinsicHallPrefactorFromMomentumMeasure e hbar * metallicBerryWeightCutoff m εF Λ

/-- Clean metallic intrinsic Hall conductivity after the UV cutoff is removed. -/
def intrinsicHallConductivity (e hbar m εF : ℝ) : ℝ :=
  intrinsicHallPrefactorFromMomentumMeasure e hbar * metallicBerryWeightUV m εF

/-- The finite-cutoff Hall conductivity converges to the clean metallic intrinsic response. -/
theorem tendsto_intrinsicHallConductivityCutoff_atTop (e hbar m εF : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) :
    Tendsto (intrinsicHallConductivityCutoff e hbar m εF) atTop
      (𝓝 (intrinsicHallConductivity e hbar m εF)) := by
  unfold intrinsicHallConductivityCutoff intrinsicHallConductivity
  exact tendsto_const_nhds.mul (tendsto_metallicBerryWeightCutoff_atTop m εF hm hmF)

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
  ring

end

end AnomalousHall.MassiveDirac
