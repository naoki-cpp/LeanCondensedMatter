import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerrySymmetry
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Intrinsic Berry weight for the metallic massive Dirac cone

This file begins the occupied-state part of #1269 without hiding the ultraviolet issue of a
single continuum Dirac cone.  After angular reduction and the change from radial momentum to the
positive Dirac energy `ε`, the dimensionless Berry-weight density of band sign `s = ±1` is

```text
-s m / (2 ε²).
```

Its primitive is `s m / (2 ε)`.  We first integrate only over finite positive energy intervals,
then combine

* the filled lower band from `m` to a finite ultraviolet cutoff `Λ`, and
* the occupied upper band from `m` to the metallic Fermi energy `εF`,

under the benchmark convention `0 < m ≤ εF ≤ Λ`.  The resulting finite-cutoff weight is

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
`p dp = E dE / v²`; hence the velocity cancels before the energy integration. -/
def radialBerryEnergyDensity (band : Band) (m ε : ℝ) : ℝ :=
  -(bandSign band * m / 2) / ε ^ 2

/-- Primitive of the radially reduced Berry-weight density on `ε ≠ 0`. -/
def radialBerryEnergyPrimitive (band : Band) (m ε : ℝ) : ℝ :=
  (bandSign band * m / 2) / ε

/-- The energy-space Berry primitive differentiates to the reduced Berry density away from zero. -/
theorem hasDerivAt_radialBerryEnergyPrimitive (band : Band) (m ε : ℝ) (hε : ε ≠ 0) :
    HasDerivAt (radialBerryEnergyPrimitive band m)
      (radialBerryEnergyDensity band m ε) ε := by
  have h := (hasDerivAt_const ε (bandSign band * m / 2)).div (hasDerivAt_id ε) hε
  simpa [radialBerryEnergyPrimitive, radialBerryEnergyDensity] using h

/-- Berry weight accumulated over a finite positive-energy shell. -/
def energyShellBerryWeight (band : Band) (m ε₀ ε₁ : ℝ) : ℝ :=
  ∫ ε in ε₀..ε₁, radialBerryEnergyDensity band m ε

/-- Exact finite-shell Berry-weight integral for `0 < ε₀ ≤ ε₁`. -/
theorem energyShellBerryWeight_eq (band : Band) (m ε₀ ε₁ : ℝ)
    (hε₀ : 0 < ε₀) (hord : ε₀ ≤ ε₁) :
    energyShellBerryWeight band m ε₀ ε₁ =
      radialBerryEnergyPrimitive band m ε₁ -
        radialBerryEnergyPrimitive band m ε₀ := by
  have hder : ∀ ε ∈ Ioo ε₀ ε₁,
      HasDerivAt (radialBerryEnergyPrimitive band m)
        (radialBerryEnergyDensity band m ε) ε := by
    intro ε hε
    exact hasDerivAt_radialBerryEnergyPrimitive band m ε (ne_of_gt (lt_trans hε₀ hε.1))
  have hcont : ContinuousOn (radialBerryEnergyPrimitive band m) (Icc ε₀ ε₁) := by
    intro ε hε
    exact (hasDerivAt_radialBerryEnergyPrimitive band m ε
      (ne_of_gt (lt_of_lt_of_le hε₀ hε.1))).continuousAt.continuousWithinAt
  have hdensity : ContinuousOn (radialBerryEnergyDensity band m) (Icc ε₀ ε₁) := by
    intro ε hε
    have hε0 : ε ≠ 0 := ne_of_gt (lt_of_lt_of_le hε₀ hε.1)
    unfold radialBerryEnergyDensity
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hε0))
  have hint : IntervalIntegrable (radialBerryEnergyDensity band m) volume ε₀ ε₁ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hord]
    exact hdensity.integrableOn_Icc
  unfold energyShellBerryWeight
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hord hcont hder hint

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
  simp [radialBerryEnergyPrimitive]
  ring

/-- Metallic upper-band contribution: `m/(2εF) - 1/2`. -/
theorem conductionBerryWeight_eq (m εF : ℝ) (hm : 0 < m) (hmF : m ≤ εF) :
    conductionBerryWeight m εF = m / (2 * εF) - 1 / 2 := by
  rw [conductionBerryWeight, energyShellBerryWeight_eq .upper m m εF hm hmF]
  simp [radialBerryEnergyPrimitive]
  ring

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
