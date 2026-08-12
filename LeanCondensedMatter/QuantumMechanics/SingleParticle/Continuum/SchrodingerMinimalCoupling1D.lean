import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise electromagnetic minimal coupling in one dimension

This module owns the local algebra of electromagnetic minimal coupling independently of probability
current and continuity proofs. For charge `q`, reduced Planck constant `ℏ`, and real vector potential
value `A`, the convention is

`D_A ψ = ∂ₓψ - i (q A / ℏ) ψ`

and hence

`π_A ψ = (-iℏ ∂ₓ - q A) ψ = -iℏ D_A ψ`.

The module also provides the pointwise square `π_A² ψ` and the minimally coupled Schrödinger
right-hand side

`(1 / (2m)) π_A² ψ + q φ ψ`.

All derivatives are supplied explicitly as pointwise values. No `L²` operator, domain,
self-adjointness, current, or continuity statement is introduced here.
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
  apply Complex.ext
  · simp [kineticMomentumValue1D, gaugeCovariantDerivativeValue1D,
      gaugeConnectionCoefficientValue1D]
    field_simp [hℏ]
  · simp [kineticMomentumValue1D, gaugeCovariantDerivativeValue1D,
      gaugeConnectionCoefficientValue1D]
    field_simp [hℏ]
    ring

/-- The value obtained by differentiating `(-iℏ ∂ₓ - q A) ψ` once in space, with `Aₓ`, `ψₓ`, and
`ψₓₓ` supplied explicitly. -/
def kineticMomentumDerivativeValue1D
    (q ℏ vectorPotential vectorPotentialDerivative : ℝ) (ψ ψx ψxx : ℂ) : ℂ :=
  -(Complex.I * (ℏ : ℂ)) * ψxx -
    ((q * vectorPotentialDerivative : ℝ) : ℂ) * ψ -
    ((q * vectorPotential : ℝ) : ℂ) * ψx

/-- Pointwise value of `(-iℏ ∂ₓ - q A)² ψ`. -/
def kineticMomentumSquaredValue1D
    (q ℏ vectorPotential vectorPotentialDerivative : ℝ) (ψ ψx ψxx : ℂ) : ℂ :=
  kineticMomentumValue1D q ℏ vectorPotential
    (kineticMomentumValue1D q ℏ vectorPotential ψ ψx)
    (kineticMomentumDerivativeValue1D q ℏ vectorPotential vectorPotentialDerivative ψ ψx ψxx)

/-- Expanding the minimally coupled kinetic momentum square gives the Laplacian term, the two
vector-potential derivative terms, and the `q² A²` term. -/
theorem kineticMomentumSquaredValue1D_eq_expanded
    (q ℏ vectorPotential vectorPotentialDerivative : ℝ) (ψ ψx ψxx : ℂ) :
    kineticMomentumSquaredValue1D q ℏ vectorPotential vectorPotentialDerivative ψ ψx ψxx =
      -((ℏ ^ 2 : ℝ) : ℂ) * ψxx +
        Complex.I * ((q * ℏ * vectorPotentialDerivative : ℝ) : ℂ) * ψ +
        2 * Complex.I * ((q * ℏ * vectorPotential : ℝ) : ℂ) * ψx +
        ((q ^ 2 * vectorPotential ^ 2 : ℝ) : ℂ) * ψ := by
  apply Complex.ext
  · simp [kineticMomentumSquaredValue1D, kineticMomentumDerivativeValue1D,
      kineticMomentumValue1D, pow_two]
    ring
  · simp [kineticMomentumSquaredValue1D, kineticMomentumDerivativeValue1D,
      kineticMomentumValue1D, pow_two]
    ring

/-- The pointwise right-hand side of the minimally coupled Schrödinger equation
`(1 / (2m)) π_A² ψ + q φ ψ`. -/
def minimallyCoupledSchrodingerRhsValue1D
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψx ψxx : ℂ) : ℂ :=
  (((1 / (2 * mass) : ℝ) : ℂ) *
      kineticMomentumSquaredValue1D q ℏ vectorPotential vectorPotentialDerivative ψ ψx ψxx) +
    ((q * scalarPotential : ℝ) : ℂ) * ψ

/-- Explicit physical expansion of the minimally coupled Schrödinger right-hand side. -/
theorem minimallyCoupledSchrodingerRhsValue1D_eq_expanded
    (q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential : ℝ)
    (ψ ψx ψxx : ℂ) (hmass : mass ≠ 0) :
    minimallyCoupledSchrodingerRhsValue1D
        q ℏ mass vectorPotential vectorPotentialDerivative scalarPotential ψ ψx ψxx =
      -((ℏ ^ 2 / (2 * mass) : ℝ) : ℂ) * ψxx +
        Complex.I * ((q * ℏ * vectorPotential / mass : ℝ) : ℂ) * ψx +
        Complex.I * ((q * ℏ * vectorPotentialDerivative / (2 * mass) : ℝ) : ℂ) * ψ +
        ((q ^ 2 * vectorPotential ^ 2 / (2 * mass) + q * scalarPotential : ℝ) : ℂ) * ψ := by
  have hmassC : (mass : ℂ) ≠ 0 := by
    exact_mod_cast hmass
  unfold minimallyCoupledSchrodingerRhsValue1D
  rw [kineticMomentumSquaredValue1D_eq_expanded]
  push_cast
  field_simp [hmassC]
  ring

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

end
end Continuum
end SingleParticle
end QuantumMechanics
