import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac radial denominator kernels

This module owns the model-local radial denominator algebra shared by Born self-energy, Born
propagators, and retarded-advanced current-rung calculations. It contains the effective-energy /
effective-mass quadratic denominator, the weak-Born retarded-advanced denominator data, and the
single-denominator polar-Jacobian kernel.

No self-energy, disorder/measure prefactor, radial integral, ladder conclusion, or conductivity
statement lives here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Radial massive-Dirac denominator for arbitrary complex effective energy and mass. -/
def massiveDiracRadialDenominator
    (v p : ℝ) (effectiveEnergy effectiveMass : ℂ) : ℂ :=
  effectiveEnergy ^ 2 - effectiveMass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)

/-- Retarded-advanced product of two radial massive-Dirac denominators. -/
def massiveDiracRetardedAdvancedRadialDenominatorProduct
    (v p : ℝ)
    (retardedEnergy retardedMass advancedEnergy advancedMass : ℂ) : ℂ :=
  massiveDiracRadialDenominator v p retardedEnergy retardedMass *
    massiveDiracRadialDenominator v p advancedEnergy advancedMass

/-- Polar Jacobian divided by one radial massive-Dirac denominator. -/
def massiveDiracRadialDenominatorKernel
    (v p : ℝ) (effectiveEnergy effectiveMass : ℂ) : ℂ :=
  (p : ℂ) * (massiveDiracRadialDenominator v p effectiveEnergy effectiveMass)⁻¹

/-- Common positive-scale expression multiplying the metallic Born scalar and `σ_z` damping
channels. Positivity requires the physical hypotheses proved downstream when needed. -/
def continuumBornDampingScale
    (v disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength / (4 * hbar ^ 2 * v ^ 2)

/-- Side-indexed effective energy after retaining the metallic Born scalar damping channel. -/
def continuumBornEffectiveEnergy
    (side : SpectralSide) (v probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (probeEnergy : ℂ) +
    ((side.sign * continuumBornDampingScale v disorderStrength hbar * probeEnergy : ℝ) : ℂ) *
      Complex.I

/-- Side-indexed effective Dirac mass after retaining the metallic Born `σ_z` damping channel. -/
def continuumBornEffectiveMass
    (side : SpectralSide) (v m disorderStrength hbar : ℝ) : ℂ :=
  (m : ℂ) -
    ((side.sign * continuumBornDampingScale v disorderStrength hbar * m : ℝ) : ℂ) *
      Complex.I

/-- Real radial center of the weak-Born retarded-advanced denominator pair. -/
def continuumBornRADenominatorCenter
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2) -
    v ^ 2 * p ^ 2

/-- Signed width parameter multiplying `i` in the weak-Born retarded denominator. -/
def continuumBornRADenominatorWidth
    (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  2 * continuumBornDampingScale v disorderStrength hbar *
    (probeEnergy ^ 2 + m ^ 2)

/-- Manifestly real weak-Born retarded-advanced denominator product. -/
def continuumBornRADenominatorProduct
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRADenominatorCenter v m p probeEnergy disorderStrength hbar ^ 2 +
    continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar ^ 2

/-- The real weak-Born retarded-advanced denominator product is nonnegative. -/
theorem continuumBornRADenominatorProduct_nonneg
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    0 ≤ continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar := by
  unfold continuumBornRADenominatorProduct
  positivity

/-- The real weak-Born radial product is the real-valued form of the canonical complex RA product. -/
theorem coe_continuumBornRADenominatorProduct_eq_massiveDirac
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (continuumBornRADenominatorProduct
        v m p probeEnergy disorderStrength hbar : ℂ) =
      massiveDiracRetardedAdvancedRadialDenominatorProduct v p
        (continuumBornEffectiveEnergy .retarded v probeEnergy disorderStrength hbar)
        (continuumBornEffectiveMass .retarded v m disorderStrength hbar)
        (continuumBornEffectiveEnergy .advanced v probeEnergy disorderStrength hbar)
        (continuumBornEffectiveMass .advanced v m disorderStrength hbar) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  simp [massiveDiracRetardedAdvancedRadialDenominatorProduct,
    massiveDiracRadialDenominator, continuumBornEffectiveEnergy, continuumBornEffectiveMass,
    continuumBornRADenominatorProduct, continuumBornRADenominatorCenter,
    continuumBornRADenominatorWidth, SpectralSide.sign]
  ring_nf
  simp [hI]
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac
