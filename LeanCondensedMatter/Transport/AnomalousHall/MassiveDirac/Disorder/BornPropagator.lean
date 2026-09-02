import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.SelfEnergyBroadeningLimit
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder Born-dressed massive-Dirac propagator

This Phase 5 bridge consumes the already-derived metallic Born damping scale and feeds both
surviving self-energy channels back into the massive-Dirac Pauli propagator.  In the zero-external-
broadening weak-disorder form used by the NCA benchmark,

```text
γ = W / (4 ℏ² v²),
ε̃_s = ε + s i γ ε,
m̃_s = m - s i γ m,
```

with `s = +1` for retarded and `s = -1` for advanced.  The opposite signs of the scalar and
`σ_z` damping channels are retained explicitly; this is not replaced by a single phenomenological
broadening.

The definitions here are model-specific Born approximation data.  They are not exact disorder-
averaged Green functions and do not introduce a second self-energy definition.  No radial
integration, ladder resummation, Ward claim, or conductivity theorem occurs here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Common positive-scale expression multiplying the metallic Born scalar and `σ_z` damping
channels.  Positivity requires the physical hypotheses proved downstream when needed. -/
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

/-- `σₓ` coefficient of the Born-dressed Pauli propagator. -/
def continuumBornPauliGreenXCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornPauliGreenDenominator
      side v m px py probeEnergy disorderStrength hbar)⁻¹ *
    ((v * px : ℝ) : ℂ)

/-- `σᵧ` coefficient of the Born-dressed Pauli propagator. -/
def continuumBornPauliGreenYCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornPauliGreenDenominator
      side v m px py probeEnergy disorderStrength hbar)⁻¹ *
    ((v * py : ℝ) : ℂ)

/-- `σ_z` coefficient of the Born-dressed Pauli propagator. -/
def continuumBornPauliGreenZCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornPauliGreenDenominator
      side v m px py probeEnergy disorderStrength hbar)⁻¹ *
    continuumBornEffectiveMass side v m disorderStrength hbar

/-- The damping scale is exactly the physical-momentum prefactor already extracted from the Born
self-energy. -/
theorem continuumBornDampingScale_eq_selfEnergyPrefactor
    (v disorderStrength hbar : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornDampingScale v disorderStrength hbar =
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) := by
  rw [continuumBornDampingPrefactor_eq disorderStrength hbar v hhbar hvelocity]
  rfl

@[simp] theorem continuumBornEffectiveEnergy_retarded
    (v probeEnergy disorderStrength hbar : ℝ) :
    continuumBornEffectiveEnergy .retarded v probeEnergy disorderStrength hbar =
      (probeEnergy : ℂ) +
        ((continuumBornDampingScale v disorderStrength hbar * probeEnergy : ℝ) : ℂ) *
          Complex.I := by
  simp [continuumBornEffectiveEnergy]

@[simp] theorem continuumBornEffectiveEnergy_advanced
    (v probeEnergy disorderStrength hbar : ℝ) :
    continuumBornEffectiveEnergy .advanced v probeEnergy disorderStrength hbar =
      (probeEnergy : ℂ) -
        ((continuumBornDampingScale v disorderStrength hbar * probeEnergy : ℝ) : ℂ) *
          Complex.I := by
  simp [continuumBornEffectiveEnergy, sub_eq_add_neg]

@[simp] theorem continuumBornEffectiveMass_retarded
    (v m disorderStrength hbar : ℝ) :
    continuumBornEffectiveMass .retarded v m disorderStrength hbar =
      (m : ℂ) -
        ((continuumBornDampingScale v disorderStrength hbar * m : ℝ) : ℂ) * Complex.I := by
  simp [continuumBornEffectiveMass]

@[simp] theorem continuumBornEffectiveMass_advanced
    (v m disorderStrength hbar : ℝ) :
    continuumBornEffectiveMass .advanced v m disorderStrength hbar =
      (m : ℂ) +
        ((continuumBornDampingScale v disorderStrength hbar * m : ℝ) : ℂ) * Complex.I := by
  simp [continuumBornEffectiveMass]

/-- Closed side-indexed form of the Born-dressed denominator used by the radial retarded-advanced
rung.  Its real part is even in the spectral side, while its imaginary part changes sign. -/
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

/-- Retarded and advanced effective energies are complex conjugates. -/
theorem star_continuumBornEffectiveEnergy_retarded_eq_advanced
    (v probeEnergy disorderStrength hbar : ℝ) :
    star (continuumBornEffectiveEnergy .retarded v probeEnergy disorderStrength hbar) =
      continuumBornEffectiveEnergy .advanced v probeEnergy disorderStrength hbar := by
  apply Complex.ext <;>
    simp [continuumBornEffectiveEnergy]

/-- Retarded and advanced effective masses are complex conjugates. -/
theorem star_continuumBornEffectiveMass_retarded_eq_advanced
    (v m disorderStrength hbar : ℝ) :
    star (continuumBornEffectiveMass .retarded v m disorderStrength hbar) =
      continuumBornEffectiveMass .advanced v m disorderStrength hbar := by
  apply Complex.ext <;>
    simp [continuumBornEffectiveMass]

/-- The Born-dressed quadratic retarded and advanced denominators are complex conjugates. -/
@[simp] theorem star_continuumBornPauliGreenDenominator_retarded_eq_advanced
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    star
        (continuumBornPauliGreenDenominator
          .retarded v m px py probeEnergy disorderStrength hbar) =
      continuumBornPauliGreenDenominator
        .advanced v m px py probeEnergy disorderStrength hbar := by
  rw [continuumBornPauliGreenDenominator_eq_closedForm,
    continuumBornPauliGreenDenominator_eq_closedForm]
  apply Complex.ext <;> simp [SpectralSide.sign]

/-- The scalar Pauli coefficient of the advanced Born propagator is the conjugate of the retarded
coefficient. -/
@[simp] theorem star_continuumBornPauliGreenScalarCoefficient_retarded_eq_advanced
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    star
        (continuumBornPauliGreenScalarCoefficient
          .retarded v m px py probeEnergy disorderStrength hbar) =
      continuumBornPauliGreenScalarCoefficient
        .advanced v m px py probeEnergy disorderStrength hbar := by
  simpa [continuumBornPauliGreenScalarCoefficient, mul_comm, sub_eq_add_neg]

/-- The `σₓ` Pauli coefficient of the advanced Born propagator is the conjugate of the retarded
coefficient. -/
@[simp] theorem star_continuumBornPauliGreenXCoefficient_retarded_eq_advanced
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    star
        (continuumBornPauliGreenXCoefficient
          .retarded v m px py probeEnergy disorderStrength hbar) =
      continuumBornPauliGreenXCoefficient
        .advanced v m px py probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenXCoefficient, mul_comm]

/-- The `σᵧ` Pauli coefficient of the advanced Born propagator is the conjugate of the retarded
coefficient. -/
@[simp] theorem star_continuumBornPauliGreenYCoefficient_retarded_eq_advanced
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    star
        (continuumBornPauliGreenYCoefficient
          .retarded v m px py probeEnergy disorderStrength hbar) =
      continuumBornPauliGreenYCoefficient
        .advanced v m px py probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenYCoefficient, mul_comm]

/-- The `σ_z` Pauli coefficient of the advanced Born propagator is the conjugate of the retarded
coefficient. -/
@[simp] theorem star_continuumBornPauliGreenZCoefficient_retarded_eq_advanced
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    star
        (continuumBornPauliGreenZCoefficient
          .retarded v m px py probeEnergy disorderStrength hbar) =
      continuumBornPauliGreenZCoefficient
        .advanced v m px py probeEnergy disorderStrength hbar := by
  simp [continuumBornPauliGreenZCoefficient, mul_comm]

end

end AnomalousHall.MassiveDirac
