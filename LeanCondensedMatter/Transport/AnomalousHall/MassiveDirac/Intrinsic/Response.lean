import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.BerrySymmetry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# Intrinsic Berry weight for the metallic massive Dirac cone

This file begins the occupied-state part of #1269 without hiding the ultraviolet issue of a
single continuum Dirac cone. After angular reduction and the change from radial momentum to the
positive Dirac energy `ε`, the dimensionless Berry-weight density of band sign `s = ±1` is

```text
-s m / (2 ε²).
```

We integrate only over finite positive energy intervals, then combine

* the filled lower band from `m` to a finite ultraviolet cutoff `Λ`, and
* the occupied upper band from `m` to the metallic Fermi energy `εF`,

under the benchmark convention `0 < m ≤ εF ≤ Λ`. The resulting finite-cutoff weight is

```text
m / (2 εF) - m / (2 Λ).
```

No infinite-cutoff limit and no `e²/h` transport prefactor are claimed in this file.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory Set
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

/-- Filled lower-band Berry weight from the positive gap edge `m` to a finite UV cutoff `Λ`.
The benchmark in #1269 takes `m > 0`. -/
def valenceBerryWeightCutoff (m Λ : ℝ) : ℝ :=
  energyShellBerryWeight .lower m m Λ

/-- Occupied upper-band Berry weight from the gap edge `m` to the metallic Fermi energy `εF`. -/
def conductionBerryWeight (m εF : ℝ) : ℝ :=
  energyShellBerryWeight .upper m m εF

/-- Finite-cutoff lower-band contribution: `1/2 - m/(2Λ)`. -/
theorem valenceBerryWeightCutoff_eq (m Λ : ℝ) (hm : 0 < m) (hmΛ : m ≤ Λ) :
    valenceBerryWeightCutoff m Λ = 1 / 2 - m / (2 * Λ) := by
  rw [valenceBerryWeightCutoff, energyShellBerryWeight_eq .lower m m Λ hm hmΛ]
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hΛ0 : Λ ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hmΛ)
  simp
  field_simp [hm0, hΛ0]
  ring

/-- Metallic upper-band contribution: `m/(2εF) - 1/2`. -/
theorem conductionBerryWeight_eq (m εF : ℝ) (hm : 0 < m) (hmF : m ≤ εF) :
    conductionBerryWeight m εF = m / (2 * εF) - 1 / 2 := by
  rw [conductionBerryWeight, energyShellBerryWeight_eq .upper m m εF hm hmF]
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hF0 : εF ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hmF)
  simp
  field_simp [hm0, hF0]

/-- Total occupied-state Berry weight with a finite valence-band ultraviolet cutoff. -/
def metallicBerryWeightCutoff (m εF Λ : ℝ) : ℝ :=
  valenceBerryWeightCutoff m Λ + conductionBerryWeight m εF

/-- The finite-cutoff metallic Berry weight keeps the single-cone regulator term explicit. -/
theorem metallicBerryWeightCutoff_eq (m εF Λ : ℝ)
    (hm : 0 < m) (hmF : m ≤ εF) (hFΛ : εF ≤ Λ) :
    metallicBerryWeightCutoff m εF Λ =
      m / (2 * εF) - m / (2 * Λ) := by
  rw [metallicBerryWeightCutoff,
    valenceBerryWeightCutoff_eq m Λ hm (hmF.trans hFΛ),
    conductionBerryWeight_eq m εF hm hmF]
  ring

end

end AnomalousHall.MassiveDirac
