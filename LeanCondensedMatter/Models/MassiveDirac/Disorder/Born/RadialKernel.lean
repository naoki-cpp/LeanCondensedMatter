import LeanCondensedMatter.Models.MassiveDirac.Propagator.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Massive-Dirac radial denominator kernels

This module owns the weak-Born retarded/advanced denominator parametrization and its
real nonnegative product. The disorder-independent complex radial denominator,
retarded/advanced product, and polar-Jacobian kernel live in
`Propagator.RadialDenominator`, which this module imports.

No self-energy, disorder/measure prefactor, radial integral, ladder conclusion, or conductivity
statement lives here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

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

end QuantumTheory.Models.MassiveDirac
