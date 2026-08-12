import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise probability and current quantities in one dimension

This module owns the dynamics-independent pointwise probability and charge quantities used by both
scalar and gauge-covariant one-particle quantum mechanics.

The canonical scalar quantities are

`ρ(ψ) = |ψ|²`

and

`pairing(ψ, χ) = Im (star ψ * χ)`.

For kinetic coefficient `κ`, the one-dimensional probability current is

`j = (2κ / ℏ) pairing(ψ, ψₓ)`.

No Schrödinger equation, potential, differentiability hypothesis, or conservation theorem is
introduced here. Coordinate `re` / `im` projections below are intrinsic descriptions of these
physical real-valued quantities, rather than conversions of values already proved real.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- Pointwise probability density `‖ψ‖²`. -/
def probabilityDensityValue (ψ : ℂ) : ℝ :=
  Complex.normSq ψ

/-- The probability density agrees with the squared complex norm. -/
theorem probabilityDensityValue_eq_norm_sq (ψ : ℂ) :
    probabilityDensityValue ψ = ‖ψ‖ ^ 2 := by
  simpa [probabilityDensityValue] using Complex.normSq_eq_norm_sq ψ

/-- The canonical real pairing underlying one-dimensional probability currents. -/
def probabilityCurrentPairingValue (ψ χ : ℂ) : ℝ :=
  (star ψ * χ).im

/-- Coordinate expansion of the canonical current pairing. -/
theorem probabilityCurrentPairingValue_eq_coordinates (ψ χ : ℂ) :
    probabilityCurrentPairingValue ψ χ = ψ.re * χ.im - ψ.im * χ.re := by
  simp [probabilityCurrentPairingValue, Complex.mul_im]
  ring

/-- Multiplying both entries of `Im (conj ψ * χ)` by the same unit-modulus phase leaves the pairing
unchanged. -/
theorem probabilityCurrentPairingValue_phase_mul
    (phase ψ χ : ℂ) (hphase : phase.re ^ 2 + phase.im ^ 2 = 1) :
    probabilityCurrentPairingValue (phase * ψ) (phase * χ) =
      probabilityCurrentPairingValue ψ χ := by
  rw [probabilityCurrentPairingValue_eq_coordinates,
    probabilityCurrentPairingValue_eq_coordinates]
  simp only [Complex.mul_re, Complex.mul_im]
  calc
    (phase.re * ψ.re - phase.im * ψ.im) *
          (phase.re * χ.im + phase.im * χ.re) -
        (phase.re * ψ.im + phase.im * ψ.re) *
          (phase.re * χ.re - phase.im * χ.im) =
      (phase.re ^ 2 + phase.im ^ 2) *
        (ψ.re * χ.im - ψ.im * χ.re) := by ring
    _ = ψ.re * χ.im - ψ.im * χ.re := by rw [hphase, one_mul]

/-- Pointwise one-dimensional probability current for kinetic coefficient `κ`.

This is `(2κ / ℏ) Im (star ψ * ψₓ)`. -/
def probabilityCurrentValue1D (ℏ κ : ℝ) (ψ ψx : ℂ) : ℝ :=
  (2 * κ / ℏ) * probabilityCurrentPairingValue ψ ψx

/-- Coordinate expansion of the one-dimensional probability current. -/
theorem probabilityCurrentValue1D_eq_coordinates
    (ℏ κ : ℝ) (ψ ψx : ℂ) :
    probabilityCurrentValue1D ℏ κ ψ ψx =
      (2 * κ / ℏ) * (ψ.re * ψx.im - ψ.im * ψx.re) := by
  rw [probabilityCurrentValue1D, probabilityCurrentPairingValue_eq_coordinates]

/-- Charge density obtained by multiplying probability density by the particle charge. -/
def chargeDensityValue (q : ℝ) (ψ : ℂ) : ℝ :=
  q * probabilityDensityValue ψ

/-- Charge current obtained by multiplying probability current by the particle charge. -/
def chargeCurrentValue1D (q ℏ κ : ℝ) (ψ ψx : ℂ) : ℝ :=
  q * probabilityCurrentValue1D ℏ κ ψ ψx

end
end Continuum
end SingleParticle
end QuantumMechanics
