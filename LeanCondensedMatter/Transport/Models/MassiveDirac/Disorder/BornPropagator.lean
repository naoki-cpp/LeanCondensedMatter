import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Damping
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.RadialKernel
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder Born-dressed massive-Dirac propagator

This module consumes the metallic Born radial data owned by `Disorder.Born.RadialKernel` and feeds
both surviving self-energy channels back into the massive-Dirac Pauli propagator. In the
zero-external-broadening weak-disorder form used by the NCA benchmark,

```text
γ = W / (4 ℏ² v²),
ε̃_s = ε + s i γ ε,
m̃_s = m - s i γ m,
```

with `s = +1` for retarded and `s = -1` for advanced. The opposite signs of the scalar and `σ_z`
damping channels are retained explicitly; this is not replaced by a single phenomenological
broadening.

The shared radial denominator pair and its real retarded-advanced product live upstream in
`Disorder.Born.RadialKernel`. This module only realizes the Cartesian propagator coefficients and
records the self-energy-prefactor and Cartesian-to-radial denominator bridges. No radial
integration, ladder resummation, Ward claim, or conductivity theorem occurs here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Continuum disorder strength corresponding exactly to a chosen Born damping scale `γ`. -/
def continuumBornDisorderStrengthOfDampingScale (v hbar gamma : ℝ) : ℝ :=
  4 * gamma * hbar ^ 2 * v ^ 2

/-- The parameterization `W(γ) = 4 γ ℏ² v²` exactly inverts the Born damping scale. -/
theorem continuumBornDampingScale_disorderStrengthOfDampingScale
    (v hbar gamma : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornDampingScale v
        (continuumBornDisorderStrengthOfDampingScale v hbar gamma) hbar = gamma := by
  unfold continuumBornDampingScale continuumBornDisorderStrengthOfDampingScale
  field_simp [hvelocity, hhbar]

/-- Quadratic denominator of the Born-dressed two-band propagator. -/
def continuumBornPauliGreenDenominator
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  continuumBornEffectiveEnergy side v probeEnergy disorderStrength hbar ^ 2 -
    continuumBornEffectiveMass side v m disorderStrength hbar ^ 2 -
    ((v ^ 2 * (px ^ 2 + py ^ 2) : ℝ) : ℂ)

/-- Identity coefficient of the Born-dressed Pauli propagator. -/
def continuumBornPauliGreenScalarCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornPauliGreenDenominator
      side v m px py probeEnergy disorderStrength hbar)⁻¹ *
    continuumBornEffectiveEnergy side v probeEnergy disorderStrength hbar

/-- Direction-indexed Pauli-vector coefficient of the Born-dressed propagator. -/
def continuumBornPauliGreenPauliCoefficient
    (axis : PauliAxis) (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornPauliGreenDenominator
      side v m px py probeEnergy disorderStrength hbar)⁻¹ *
    InternalSpace.pauliAxisComponent axis
      (((v * px : ℝ) : ℂ))
      (((v * py : ℝ) : ℂ))
      (continuumBornEffectiveMass side v m disorderStrength hbar)

/-- The damping scale is exactly the physical-momentum prefactor already extracted from the Born
self-energy. -/
theorem continuumBornDampingScale_eq_selfEnergyPrefactor
    (v disorderStrength hbar : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornDampingScale v disorderStrength hbar =
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) := by
  rw [continuumBornDampingPrefactor_eq disorderStrength hbar v hhbar hvelocity]
  rfl

/-- Closed side-indexed form of the Born-dressed denominator used by the radial retarded-advanced
rung. Its real part is even in the spectral side, while its imaginary part changes sign. -/
theorem continuumBornPauliGreenDenominator_eq_closedForm
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenDenominator
        side v m px py probeEnergy disorderStrength hbar =
      (((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2) -
          v ^ 2 * (px ^ 2 + py ^ 2) : ℝ) : ℂ) +
        ((2 * side.sign * continuumBornDampingScale v disorderStrength hbar *
            (probeEnergy ^ 2 + m ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  cases side <;>
    simp [continuumBornPauliGreenDenominator, continuumBornEffectiveEnergy,
      continuumBornEffectiveMass, SpectralSide.sign] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

/-- The radial Cartesian Born denominators multiply to the canonical real weak-Born RA product. -/
theorem continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenDenominator
        .retarded v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenDenominator
        .advanced v m p 0 probeEnergy disorderStrength hbar =
      (continuumBornRADenominatorProduct
        v m p probeEnergy disorderStrength hbar : ℂ) := by
  rw [coe_continuumBornRADenominatorProduct_eq_massiveDirac]
  simp [massiveDiracRetardedAdvancedRadialDenominatorProduct,
    massiveDiracRadialDenominator, continuumBornPauliGreenDenominator]

end

end QuantumTheory.Transport.Models.MassiveDirac
