import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise Schrödinger continuity equation in one space dimension

This module derives the local probability-current balance from the scalar-potential
nonrelativistic Schrödinger equation without treating the Laplacian as a bounded operator on `L²`.
The first slice is deliberately pointwise and one-dimensional. It separates the calculus identities
from the algebraic cancellation in the equation of motion, so a later weak formulation can reuse the
same kernel with explicit Sobolev and integration-by-parts hypotheses.

Write the kinetic coefficient as `κ = ℏ² / (2m)`. At one spacetime point the Schrödinger equation is

`i ℏ ψₜ = -κ ψₓₓ + V ψ`,

where `V : ℝ`. Probability density and current are real-valued:

`ρ = |ψ|²`,
`j = (2κ / ℏ) Im (star ψ * ψₓ)`.

After substituting `κ = ℏ² / (2m)`, the current is the standard
`(ℏ / m) Im (star ψ * ψₓ)`. Keeping `κ` explicit makes the local cancellation independent of the
later mass parametrization.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- Real-coordinate access used only inside the explicit coordinate implementation. -/
private def realPart (z : ℂ) : ℝ :=
  z.re

/-- Imaginary-coordinate access used only inside the explicit coordinate implementation. -/
private def imaginaryPart (z : ℂ) : ℝ :=
  z.im

/-- Pointwise probability density `|ψ|²`, written in real coordinates. -/
def probabilityDensityValue (ψ : ℂ) : ℝ :=
  Complex.normSq ψ

/-- Coordinate expansion of the canonical probability-density representation. -/
theorem probabilityDensityValue_eq_coordinates (ψ : ℂ) :
    probabilityDensityValue ψ = ψ.re ^ 2 + ψ.im ^ 2 := by
  simp [probabilityDensityValue, Complex.normSq_apply, pow_two]

/-- The canonical real pairing underlying the one-dimensional probability current. -/
def probabilityCurrentPairingValue (ψ χ : ℂ) : ℝ :=
  (star ψ * χ).im

/-- Coordinate expansion of the canonical current pairing. -/
theorem probabilityCurrentPairingValue_eq_coordinates (ψ χ : ℂ) :
    probabilityCurrentPairingValue ψ χ = ψ.re * χ.im - ψ.im * χ.re := by
  simp [probabilityCurrentPairingValue, Complex.mul_im]

/-- Pointwise one-dimensional probability current for kinetic coefficient `κ`.

This is `(2κ / ℏ) Im (star ψ * ψₓ)`, expanded into real coordinates. -/
def probabilityCurrentValue1D (ℏ κ : ℝ) (ψ ψx : ℂ) : ℝ :=
  (2 * κ / ℏ) * probabilityCurrentPairingValue ψ ψx

/-- Coordinate expansion of the one-dimensional probability current. -/
theorem probabilityCurrentValue1D_eq_coordinates
    (ℏ κ : ℝ) (ψ ψx : ℂ) :
    probabilityCurrentValue1D ℏ κ ψ ψx =
      (2 * κ / ℏ) * (ψ.re * ψx.im - ψ.im * ψx.re) := by
  rw [probabilityCurrentValue1D, probabilityCurrentPairingValue_eq_coordinates]

/-- The value obtained by differentiating probability density in time. -/
def probabilityDensityTimeDerivativeValue (ψ ψt : ℂ) : ℝ :=
  2 * (ψ.re * ψt.re + ψ.im * ψt.im)

/-- Coordinate expansion of the probability-density time derivative. -/
theorem probabilityDensityTimeDerivativeValue_eq_coordinates (ψ ψt : ℂ) :
    probabilityDensityTimeDerivativeValue ψ ψt =
      2 * (ψ.re * ψt.re + ψ.im * ψt.im) := by
  rfl

/-- The value obtained by differentiating the one-dimensional probability current in space. -/
def probabilityCurrentDivergenceValue1D (ℏ κ : ℝ) (ψ ψxx : ℂ) : ℝ :=
  (2 * κ / ℏ) * probabilityCurrentPairingValue ψ ψxx

/-- Coordinate expansion of the one-dimensional probability-current divergence. -/
theorem probabilityCurrentDivergenceValue1D_eq_coordinates
    (ℏ κ : ℝ) (ψ ψxx : ℂ) :
    probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx =
      (2 * κ / ℏ) * (ψ.re * ψxx.im - ψ.im * ψxx.re) := by
  rw [probabilityCurrentDivergenceValue1D, probabilityCurrentPairingValue_eq_coordinates]

/-- Coordinatewise differentiability gives the expected real probability-density derivative.

The coordinate hypotheses are explicit in this first pointwise layer. A later convenience theorem
may bundle them behind a stable complex-to-real differentiability bridge. -/
theorem hasDerivAt_probabilityDensityValue
    {ψ : ℝ → ℂ} {ψt : ℂ} {t : ℝ}
    (hre : HasDerivAt (fun s => realPart (ψ s)) (realPart ψt) t)
    (him : HasDerivAt (fun s => imaginaryPart (ψ s)) (imaginaryPart ψt) t) :
    HasDerivAt (fun s => probabilityDensityValue (ψ s))
      (probabilityDensityTimeDerivativeValue (ψ t) ψt) t := by
  have hraw := HasDerivAt.add (HasDerivAt.mul hre hre) (HasDerivAt.mul him him)
  have hderiv :
      (realPart ψt * realPart (ψ t) + realPart (ψ t) * realPart ψt) +
          (imaginaryPart ψt * imaginaryPart (ψ t) +
            imaginaryPart (ψ t) * imaginaryPart ψt) =
        probabilityDensityTimeDerivativeValue (ψ t) ψt := by
    simp [probabilityDensityTimeDerivativeValue, realPart, imaginaryPart]
    ring
  rw [hderiv] at hraw
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hraw
  simpa [probabilityDensityValue, pow_two, Pi.mul_apply, Pi.add_apply] using hraw

/-- Differentiating the standard one-dimensional current cancels the two mixed first-derivative
terms, leaving only the second spatial derivative. -/
theorem hasDerivAt_probabilityCurrentValue1D
    (ℏ κ : ℝ) {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hψre : HasDerivAt (fun y => realPart (ψ y)) (realPart (ψx x)) x)
    (hψim : HasDerivAt (fun y => imaginaryPart (ψ y)) (imaginaryPart (ψx x)) x)
    (hψxre : HasDerivAt (fun y => realPart (ψx y)) (realPart ψxx) x)
    (hψxim : HasDerivAt (fun y => imaginaryPart (ψx y)) (imaginaryPart ψxx) x) :
    HasDerivAt (fun y => probabilityCurrentValue1D ℏ κ (ψ y) (ψx y))
      (probabilityCurrentDivergenceValue1D ℏ κ (ψ x) ψxx) x := by
  have hraw := HasDerivAt.sub
    (HasDerivAt.mul hψre hψxim) (HasDerivAt.mul hψim hψxre)
  have hderiv :
      (realPart (ψx x) * imaginaryPart (ψx x) +
            realPart (ψ x) * imaginaryPart ψxx) -
          (imaginaryPart (ψx x) * realPart (ψx x) +
            imaginaryPart (ψ x) * realPart ψxx) =
        realPart (ψ x) * imaginaryPart ψxx -
          imaginaryPart (ψ x) * realPart ψxx := by
    ring
  rw [hderiv] at hraw
  have hscaled := hraw.const_mul (2 * κ / ℏ)
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hscaled
  simpa [realPart, imaginaryPart, probabilityCurrentValue1D_eq_coordinates,
    probabilityCurrentDivergenceValue1D_eq_coordinates, Pi.mul_apply, Pi.sub_apply] using hscaled

/-- Real and imaginary component equations extracted from the pointwise Schrödinger equation. -/
theorem schrodinger_component_equations
    (ℏ κ potential : ℝ) (ψ ψt ψxx : ℂ)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt = -(κ : ℂ) * ψxx + (potential : ℂ) * ψ) :
    ℏ * ψt.im = κ * ψxx.re - potential * ψ.re ∧
      ℏ * ψt.re = -κ * ψxx.im + potential * ψ.im := by
  have hre := congrArg Complex.re hschrodinger
  have him := congrArg Complex.im hschrodinger
  simp at hre him
  constructor
  · linear_combination -hre
  · linear_combination him

/-- The local probability balance from the two real component equations. -/
theorem probability_continuity_balance_of_components
    (ℏ κ potential : ℝ) (ψ ψt ψxx : ℂ) (hℏ : ℏ ≠ 0)
    (hreal : ℏ * ψt.im = κ * ψxx.re - potential * ψ.re)
    (himag : ℏ * ψt.re = -κ * ψxx.im + potential * ψ.im) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx = 0 := by
  unfold probabilityDensityTimeDerivativeValue probabilityCurrentDivergenceValue1D
  rw [probabilityCurrentPairingValue_eq_coordinates]
  field_simp [hℏ]
  linear_combination 2 * ψ.re * himag + 2 * ψ.im * hreal

/-- Pointwise continuity balance derived directly from the nonrelativistic Schrödinger equation with
a real scalar potential. -/
theorem probability_continuity_balance_of_schrodinger
    (ℏ κ potential : ℝ) (ψ ψt ψxx : ℂ) (hℏ : ℏ ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt = -(κ : ℂ) * ψxx + (potential : ℂ) * ψ) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx = 0 := by
  rcases schrodinger_component_equations ℏ κ potential ψ ψt ψxx hschrodinger with
    ⟨hreal, himag⟩
  exact probability_continuity_balance_of_components
    ℏ κ potential ψ ψt ψxx hℏ hreal himag

/-- One-dimensional pointwise continuity equation for coordinatewise differentiable time and space
slices of a wavefunction.

The two supplied functions represent the time slice through a fixed spatial point and the spatial
slice at a fixed time. `hsame` identifies their value at the spacetime point under consideration.
No `L²` completion or unbounded-operator assertion is used. -/
theorem oneDimensional_schrodinger_continuity
    (ℏ κ potential : ℝ) (hℏ : ℏ ≠ 0)
    {ψTime ψSpace ψx : ℝ → ℂ} {ψt ψxx : ℂ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htimeRe : HasDerivAt (fun s => realPart (ψTime s)) (realPart ψt) t)
    (htimeIm : HasDerivAt (fun s => imaginaryPart (ψTime s)) (imaginaryPart ψt) t)
    (hspaceRe : HasDerivAt (fun y => realPart (ψSpace y)) (realPart (ψx x)) x)
    (hspaceIm : HasDerivAt (fun y => imaginaryPart (ψSpace y)) (imaginaryPart (ψx x)) x)
    (hspaceDerivativeRe : HasDerivAt (fun y => realPart (ψx y)) (realPart ψxx) x)
    (hspaceDerivativeIm : HasDerivAt (fun y => imaginaryPart (ψx y)) (imaginaryPart ψxx) x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * ψxx + (potential : ℂ) * ψSpace x) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace y) (ψx y)) x = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htimeRe htimeIm).deriv,
    (hasDerivAt_probabilityCurrentValue1D ℏ κ hspaceRe hspaceIm
      hspaceDerivativeRe hspaceDerivativeIm).deriv]
  rw [hsame]
  exact probability_continuity_balance_of_schrodinger
    ℏ κ potential (ψSpace x) ψt ψxx hℏ hschrodinger

/-- Charge density obtained by multiplying probability density by the particle charge. -/
def chargeDensityValue (q : ℝ) (ψ : ℂ) : ℝ :=
  q * probabilityDensityValue ψ

/-- Charge current obtained by multiplying probability current by the particle charge. -/
def chargeCurrentValue1D (q ℏ κ : ℝ) (ψ ψx : ℂ) : ℝ :=
  q * probabilityCurrentValue1D ℏ κ ψ ψx

/-- Probability-current balance immediately implies charge-current balance. -/
theorem charge_continuity_balance_of_probability
    (q densityTimeDerivative currentDivergence : ℝ)
    (hcontinuity : densityTimeDerivative + currentDivergence = 0) :
    q * densityTimeDerivative + q * currentDivergence = 0 := by
  rw [← mul_add, hcontinuity, mul_zero]

end
end Continuum
end SingleParticle
end QuantumMechanics
