import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Basic1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Electromagnetic.MinimalCoupling1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gauge-covariant one-dimensional Schrödinger current

This module owns electromagnetic probability and charge current after the pointwise minimal-coupling
kinematics have been fixed by `SchrodingerMinimalCoupling1D`.

For the convention

`D_A ψ = ∂ₓψ - i (q A / ℏ) ψ`,

the probability current is

`j = (ℏ / m) Im (conj ψ * D_A ψ)`

with expanded form

`j = (ℏ / m) Im (conj ψ * ∂ₓψ) - (q / m) A |ψ|²`.

This module also proves local gauge invariance of probability and charge current. It does not define
the minimally coupled Schrödinger equation or prove a continuity equation.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

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
  unfold electromagneticProbabilityCurrentValue1D
  rw [probabilityCurrentPairingValue_eq_coordinates,
    gaugeCovariantDerivativeValue1D_re, gaugeCovariantDerivativeValue1D_im,
    probabilityDensityValue, Complex.normSq_apply]
  unfold gaugeConnectionCoefficientValue1D
  field_simp [hℏ, hmass]
  ring

/-- With zero vector potential, the electromagnetic current reduces exactly to the pointwise
probability current with `κ = ℏ² / (2m)`. -/
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

/-- The electromagnetic probability current is invariant under the local gauge transformation of
the minimal-coupling layer. -/
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
