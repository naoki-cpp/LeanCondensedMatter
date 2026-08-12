import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gauge-covariant one-dimensional Schrödinger current

This module fixes the local minimal-coupling conventions used by the electromagnetic extension of
the continuum Schrödinger continuity equation.  For charge `q`, reduced Planck constant `ℏ`, and
real vector potential value `A`, the covariant derivative is

`D_A ψ = ∂ₓψ - i (q A / ℏ) ψ`,

so that the kinetic momentum is

`-iℏ D_A ψ = (-iℏ ∂ₓ - q A) ψ`.

The corresponding probability current is written directly through the covariant derivative.  Its
expanded form is

`j = (ℏ / m) Im (conj ψ * ∂ₓψ) - (q / m) A |ψ|²`.

Everything here is pointwise.  No magnetic Schrödinger operator on `L²`, domain statement, or
self-adjointness claim is made.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- The real minimal-coupling coefficient `q A / ℏ` at one spatial point. -/
def gaugeConnectionCoefficientValue1D (q ℏ vectorPotential : ℝ) : ℝ :=
  q * vectorPotential / ℏ

/-- Pointwise gauge-covariant derivative for the convention
`(-iℏ ∂ₓ - q A) = -iℏ D_A`. -/
def gaugeCovariantDerivativeValue1D
    (q ℏ vectorPotential : ℝ) (ψ ψx : ℂ) : ℂ :=
  ψx - Complex.I * (gaugeConnectionCoefficientValue1D q ℏ vectorPotential : ℂ) * ψ

@[simp]
theorem gaugeCovariantDerivativeValue1D_re
    (q ℏ vectorPotential : ℝ) (ψ ψx : ℂ) :
    (gaugeCovariantDerivativeValue1D q ℏ vectorPotential ψ ψx).re =
      ψx.re + gaugeConnectionCoefficientValue1D q ℏ vectorPotential * ψ.im := by
  simp [gaugeCovariantDerivativeValue1D]

@[simp]
theorem gaugeCovariantDerivativeValue1D_im
    (q ℏ vectorPotential : ℝ) (ψ ψx : ℂ) :
    (gaugeCovariantDerivativeValue1D q ℏ vectorPotential ψ ψx).im =
      ψx.im - gaugeConnectionCoefficientValue1D q ℏ vectorPotential * ψ.re := by
  simp [gaugeCovariantDerivativeValue1D]

/-- Pointwise kinetic momentum `(-iℏ ∂ₓ - q A) ψ`. -/
def kineticMomentumValue1D
    (q ℏ vectorPotential : ℝ) (ψ ψx : ℂ) : ℂ :=
  -(Complex.I * (ℏ : ℂ)) * ψx - ((q * vectorPotential : ℝ) : ℂ) * ψ

/-- The explicit minimal-coupling momentum is exactly `-iℏ D_A`. -/
theorem kineticMomentumValue1D_eq_neg_I_hbar_mul_covariantDerivative
    (q ℏ vectorPotential : ℝ) (ψ ψx : ℂ) (hℏ : ℏ ≠ 0) :
    kineticMomentumValue1D q ℏ vectorPotential ψ ψx =
      -(Complex.I * (ℏ : ℂ)) *
        gaugeCovariantDerivativeValue1D q ℏ vectorPotential ψ ψx := by
  unfold kineticMomentumValue1D gaugeCovariantDerivativeValue1D
    gaugeConnectionCoefficientValue1D
  push_cast
  field_simp [hℏ]
  simp [pow_two]

/-- The real bilinear pairing `Im (conj ψ * χ)` in coordinate form. -/
def probabilityCurrentPairingValue (ψ χ : ℂ) : ℝ :=
  ψ.re * χ.im - ψ.im * χ.re

private theorem probabilityDensityValue_eq_coordinates (ψ : ℂ) :
    probabilityDensityValue ψ = ψ.re ^ 2 + ψ.im ^ 2 :=
  rfl

private theorem probabilityCurrentValue1D_eq_coordinates
    (ℏ κ : ℝ) (ψ ψx : ℂ) :
    probabilityCurrentValue1D ℏ κ ψ ψx =
      (2 * κ / ℏ) * (ψ.re * ψx.im - ψ.im * ψx.re) :=
  rfl

/-- Electromagnetic probability current in one dimension, expressed through the covariant
derivative. -/
def electromagneticProbabilityCurrentValue1D
    (q ℏ mass vectorPotential : ℝ) (ψ ψx : ℂ) : ℝ :=
  (ℏ / mass) * probabilityCurrentPairingValue ψ
    (gaugeCovariantDerivativeValue1D q ℏ vectorPotential ψ ψx)

/-- The covariant current expands to the standard paramagnetic plus vector-potential terms. -/
theorem electromagneticProbabilityCurrentValue1D_eq_expanded
    (q ℏ mass vectorPotential : ℝ) (ψ ψx : ℂ)
    (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0) :
    electromagneticProbabilityCurrentValue1D q ℏ mass vectorPotential ψ ψx =
      (ℏ / mass) * (ψ.re * ψx.im - ψ.im * ψx.re) -
        (q / mass) * vectorPotential * probabilityDensityValue ψ := by
  unfold electromagneticProbabilityCurrentValue1D probabilityCurrentPairingValue
  rw [gaugeCovariantDerivativeValue1D_re, gaugeCovariantDerivativeValue1D_im,
    probabilityDensityValue_eq_coordinates]
  unfold gaugeConnectionCoefficientValue1D
  field_simp [hℏ, hmass]
  ring

/-- With zero vector potential, the electromagnetic current reduces exactly to the scalar-potential
current from the existing continuity API, with `κ = ℏ² / (2m)`. -/
theorem electromagneticProbabilityCurrentValue1D_zero_vectorPotential
    (q ℏ mass : ℝ) (ψ ψx : ℂ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0) :
    electromagneticProbabilityCurrentValue1D q ℏ mass 0 ψ ψx =
      probabilityCurrentValue1D ℏ (ℏ ^ 2 / (2 * mass)) ψ ψx := by
  rw [electromagneticProbabilityCurrentValue1D_eq_expanded
    q ℏ mass 0 ψ ψx hℏ hmass]
  rw [probabilityCurrentValue1D_eq_coordinates]
  simp only [mul_zero, zero_mul, sub_zero]
  have hcoeff :
      ℏ / mass = 2 * (ℏ ^ 2 / (2 * mass)) / ℏ := by
    field_simp [hℏ, hmass]
  rw [hcoeff]

/-- Electromagnetic charge current obtained by multiplying the gauge-covariant probability current
by the particle charge. -/
def electromagneticChargeCurrentValue1D
    (q ℏ mass vectorPotential : ℝ) (ψ ψx : ℂ) : ℝ :=
  q * electromagneticProbabilityCurrentValue1D q ℏ mass vectorPotential ψ ψx

/-- Charge-current scaling is definitionally the same `j_q = q j` relation as in the scalar case. -/
@[simp]
theorem electromagneticChargeCurrentValue1D_eq_charge_mul_probabilityCurrent
    (q ℏ mass vectorPotential : ℝ) (ψ ψx : ℂ) :
    electromagneticChargeCurrentValue1D q ℏ mass vectorPotential ψ ψx =
      q * electromagneticProbabilityCurrentValue1D q ℏ mass vectorPotential ψ ψx :=
  rfl

/-- Multiplying both entries of `Im (conj ψ * χ)` by the same unit-modulus phase leaves the pairing
unchanged.  The phase condition is written pointwise in real coordinates so this lemma does not
commit the API to a particular gauge-function representation. -/
theorem probabilityCurrentPairingValue_phase_mul
    (phase ψ χ : ℂ) (hphase : phase.re ^ 2 + phase.im ^ 2 = 1) :
    probabilityCurrentPairingValue (phase * ψ) (phase * χ) =
      probabilityCurrentPairingValue ψ χ := by
  unfold probabilityCurrentPairingValue
  simp only [Complex.mul_re, Complex.mul_im]
  calc
    (phase.re * ψ.re - phase.im * ψ.im) *
          (phase.re * χ.im + phase.im * χ.re) -
        (phase.re * ψ.im + phase.im * ψ.re) *
          (phase.re * χ.re - phase.im * χ.im) =
      (phase.re ^ 2 + phase.im ^ 2) *
        (ψ.re * χ.im - ψ.im * χ.re) := by ring
    _ = ψ.re * χ.im - ψ.im * χ.re := by rw [hphase, one_mul]

/-- Local gauge covariance of the covariant derivative.

If the wavefunction is multiplied by a phase and its derivative acquires the corresponding
`+ i(q/ℏ)(∂ₓχ) ψ` term while `A` shifts by `∂ₓχ`, then `D_A ψ` transforms by the same phase. -/
theorem gaugeCovariantDerivativeValue1D_gauge_transform
    (q ℏ vectorPotential gaugeDerivative : ℝ) (phase ψ ψx : ℂ) (hℏ : ℏ ≠ 0) :
    gaugeCovariantDerivativeValue1D q ℏ (vectorPotential + gaugeDerivative)
        (phase * ψ)
        (phase *
          (ψx + Complex.I *
            (gaugeConnectionCoefficientValue1D q ℏ gaugeDerivative : ℂ) * ψ)) =
      phase * gaugeCovariantDerivativeValue1D q ℏ vectorPotential ψ ψx := by
  unfold gaugeCovariantDerivativeValue1D gaugeConnectionCoefficientValue1D
  push_cast
  field_simp [hℏ]
  ring

/-- The minimally coupled kinetic momentum transforms covariantly under the same local gauge data. -/
theorem kineticMomentumValue1D_gauge_transform
    (q ℏ vectorPotential gaugeDerivative : ℝ) (phase ψ ψx : ℂ) (hℏ : ℏ ≠ 0) :
    kineticMomentumValue1D q ℏ (vectorPotential + gaugeDerivative)
        (phase * ψ)
        (phase *
          (ψx + Complex.I *
            (gaugeConnectionCoefficientValue1D q ℏ gaugeDerivative : ℂ) * ψ)) =
      phase * kineticMomentumValue1D q ℏ vectorPotential ψ ψx := by
  rw [kineticMomentumValue1D_eq_neg_I_hbar_mul_covariantDerivative
      q ℏ (vectorPotential + gaugeDerivative) (phase * ψ)
      (phase *
        (ψx + Complex.I *
          (gaugeConnectionCoefficientValue1D q ℏ gaugeDerivative : ℂ) * ψ)) hℏ]
  rw [gaugeCovariantDerivativeValue1D_gauge_transform
      q ℏ vectorPotential gaugeDerivative phase ψ ψx hℏ]
  rw [kineticMomentumValue1D_eq_neg_I_hbar_mul_covariantDerivative
      q ℏ vectorPotential ψ ψx hℏ]
  ring

/-- The electromagnetic probability current is invariant under the local gauge transformation data
used above. -/
theorem electromagneticProbabilityCurrentValue1D_gauge_invariant
    (q ℏ mass vectorPotential gaugeDerivative : ℝ) (phase ψ ψx : ℂ)
    (hℏ : ℏ ≠ 0) (hphase : phase.re ^ 2 + phase.im ^ 2 = 1) :
    electromagneticProbabilityCurrentValue1D q ℏ mass
        (vectorPotential + gaugeDerivative) (phase * ψ)
        (phase *
          (ψx + Complex.I *
            (gaugeConnectionCoefficientValue1D q ℏ gaugeDerivative : ℂ) * ψ)) =
      electromagneticProbabilityCurrentValue1D q ℏ mass vectorPotential ψ ψx := by
  unfold electromagneticProbabilityCurrentValue1D
  rw [gaugeCovariantDerivativeValue1D_gauge_transform
      q ℏ vectorPotential gaugeDerivative phase ψ ψx hℏ]
  rw [probabilityCurrentPairingValue_phase_mul phase ψ
      (gaugeCovariantDerivativeValue1D q ℏ vectorPotential ψ ψx) hphase]

/-- Gauge invariance of charge current follows immediately from probability-current invariance. -/
theorem electromagneticChargeCurrentValue1D_gauge_invariant
    (q ℏ mass vectorPotential gaugeDerivative : ℝ) (phase ψ ψx : ℂ)
    (hℏ : ℏ ≠ 0) (hphase : phase.re ^ 2 + phase.im ^ 2 = 1) :
    electromagneticChargeCurrentValue1D q ℏ mass
        (vectorPotential + gaugeDerivative) (phase * ψ)
        (phase *
          (ψx + Complex.I *
            (gaugeConnectionCoefficientValue1D q ℏ gaugeDerivative : ℂ) * ψ)) =
      electromagneticChargeCurrentValue1D q ℏ mass vectorPotential ψ ψx := by
  unfold electromagneticChargeCurrentValue1D
  rw [electromagneticProbabilityCurrentValue1D_gauge_invariant
      q ℏ mass vectorPotential gaugeDerivative phase ψ ψx hℏ hphase]

end
end Continuum
end SingleParticle
end QuantumMechanics
