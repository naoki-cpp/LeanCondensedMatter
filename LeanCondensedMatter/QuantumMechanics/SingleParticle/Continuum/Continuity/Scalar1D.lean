import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Basic1D
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise Schrödinger continuity equation in one space dimension

This module derives the local probability-current balance from the scalar-potential
nonrelativistic Schrödinger equation without treating the Laplacian as a bounded operator on `L²`.
The dynamics-independent probability density, current pairing, current, and charge quantities live
in `Probability/Basic1D`; this module owns their derivative identities and the Schrödinger-specific
cancellation.

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
    (hre : HasDerivAt (fun s => (ψ s).re) ψt.re t)
    (him : HasDerivAt (fun s => (ψ s).im) ψt.im t) :
    HasDerivAt (fun s => probabilityDensityValue (ψ s))
      (probabilityDensityTimeDerivativeValue (ψ t) ψt) t := by
  have hraw := HasDerivAt.add (HasDerivAt.mul hre hre) (HasDerivAt.mul him him)
  have hderiv :
      (ψt.re * (ψ t).re + (ψ t).re * ψt.re) +
          (ψt.im * (ψ t).im + (ψ t).im * ψt.im) =
        probabilityDensityTimeDerivativeValue (ψ t) ψt := by
    simp [probabilityDensityTimeDerivativeValue]
    ring
  rw [hderiv] at hraw
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hraw
  simpa [probabilityDensityValue, Complex.normSq_apply, pow_two, Pi.mul_apply, Pi.add_apply]
    using hraw

/-- Differentiating the standard one-dimensional current cancels the two mixed first-derivative
terms, leaving only the second spatial derivative. -/
theorem hasDerivAt_probabilityCurrentValue1D
    (ℏ κ : ℝ) {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hψre : HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : HasDerivAt (fun y => (ψx y).re) ψxx.re x)
    (hψxim : HasDerivAt (fun y => (ψx y).im) ψxx.im x) :
    HasDerivAt (fun y => probabilityCurrentValue1D ℏ κ (ψ y) (ψx y))
      (probabilityCurrentDivergenceValue1D ℏ κ (ψ x) ψxx) x := by
  have hraw := HasDerivAt.sub
    (HasDerivAt.mul hψre hψxim) (HasDerivAt.mul hψim hψxre)
  have hderiv :
      ((ψx x).re * (ψx x).im + (ψ x).re * ψxx.im) -
          ((ψx x).im * (ψx x).re + (ψ x).im * ψxx.re) =
        (ψ x).re * ψxx.im - (ψ x).im * ψxx.re := by
    ring
  rw [hderiv] at hraw
  have hscaled := hraw.const_mul (2 * κ / ℏ)
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at hscaled
  simpa [probabilityCurrentValue1D_eq_coordinates,
    probabilityCurrentDivergenceValue1D_eq_coordinates, Pi.mul_apply, Pi.sub_apply] using hscaled

/-- Real and imaginary component equations extracted from the pointwise Schrödinger equation. -/
private theorem schrodinger_component_equations
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
private theorem probability_continuity_balance_of_components
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
    (htimeRe : HasDerivAt (fun s => (ψTime s).re) ψt.re t)
    (htimeIm : HasDerivAt (fun s => (ψTime s).im) ψt.im t)
    (hspaceRe : HasDerivAt (fun y => (ψSpace y).re) (ψx x).re x)
    (hspaceIm : HasDerivAt (fun y => (ψSpace y).im) (ψx x).im x)
    (hspaceDerivativeRe : HasDerivAt (fun y => (ψx y).re) ψxx.re x)
    (hspaceDerivativeIm : HasDerivAt (fun y => (ψx y).im) ψxx.im x)
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
