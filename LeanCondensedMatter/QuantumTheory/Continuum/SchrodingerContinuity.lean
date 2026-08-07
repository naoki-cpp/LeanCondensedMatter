import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
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

where `V : ℝ`. The probability density and current are represented as complex scalars

`ρ = star ψ * ψ`,
`j = -(i κ / ℏ) (star ψ * ψₓ - ψ * star ψₓ)`.

The latter is the standard `ℏ / (2mi)` expression after substituting `κ = ℏ² / (2m)` and assuming
nonzero physical parameters. This file keeps `κ` explicit because it makes the local cancellation
independent of the later mass parametrization.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

/-- Pointwise probability density, represented in `ℂ` as `ψ† ψ`. -/
def probabilityDensityValue (ψ : ℂ) : ℂ :=
  star ψ * ψ

/-- Pointwise one-dimensional probability current for kinetic coefficient `κ`.

For `κ = ℏ² / (2m)`, this is the usual
`(ℏ / (2mi)) (star ψ * ψₓ - ψ * star ψₓ)`. -/
def probabilityCurrentValue1D (ℏ κ : ℝ) (ψ ψx : ℂ) : ℂ :=
  (-(Complex.I * (κ : ℂ) / (ℏ : ℂ))) *
    (star ψ * ψx - ψ * star ψx)

/-- The value obtained by differentiating the probability density in time. -/
def probabilityDensityTimeDerivativeValue (ψ ψt : ℂ) : ℂ :=
  star ψt * ψ + star ψ * ψt

/-- The value obtained by differentiating the one-dimensional probability current in space. -/
def probabilityCurrentDivergenceValue1D (ℏ κ : ℝ) (ψ ψxx : ℂ) : ℂ :=
  (-(Complex.I * (κ : ℂ) / (ℏ : ℂ))) *
    (star ψ * ψxx - ψ * star ψxx)

/-- The Schrödinger time derivative solved explicitly for `ψₜ`.

The scalar potential is real, which is exactly the hypothesis needed for its contribution to cancel
from the density derivative. -/
def schrodingerTimeDerivativeValue
    (ℏ κ potential : ℝ) (ψ ψxx : ℂ) : ℂ :=
  (Complex.I * (κ : ℂ) / (ℏ : ℂ)) * ψxx -
    (Complex.I * (potential : ℂ) / (ℏ : ℂ)) * ψ

/-- A differentiable complex wave amplitude has the expected density derivative. -/
theorem hasDerivAt_probabilityDensityValue
    {ψ : ℝ → ℂ} {ψt : ℂ} {t : ℝ} (hψ : HasDerivAt ψ ψt t) :
    HasDerivAt (fun s => probabilityDensityValue (ψ s))
      (probabilityDensityTimeDerivativeValue (ψ t) ψt) t := by
  with_reducible_and_instances
    simpa [probabilityDensityValue, probabilityDensityTimeDerivativeValue] using hψ.star.mul hψ

/-- Differentiating the standard one-dimensional current cancels the two mixed first-derivative
terms, leaving only the second spatial derivative. -/
theorem hasDerivAt_probabilityCurrentValue1D
    (ℏ κ : ℝ) {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hψ : HasDerivAt ψ (ψx x) x) (hψx : HasDerivAt ψx ψxx x) :
    HasDerivAt (fun y => probabilityCurrentValue1D ℏ κ (ψ y) (ψx y))
      (probabilityCurrentDivergenceValue1D ℏ κ (ψ x) ψxx) x := by
  with_reducible_and_instances
    have hbracket :
        HasDerivAt
          (fun y => star (ψ y) * ψx y - ψ y * star (ψx y))
          (star (ψ x) * ψxx - ψ x * star ψxx) x := by
      convert (hψ.star.mul hψx).sub (hψ.mul hψx.star) using 1 <;> ring_nf
    simpa [probabilityCurrentValue1D, probabilityCurrentDivergenceValue1D] using
      hbracket.const_mul (-(Complex.I * (κ : ℂ) / (ℏ : ℂ)))

/-- The local continuity balance after substituting the solved Schrödinger time derivative.

The real scalar-potential terms cancel exactly. -/
theorem probability_continuity_balance_solved
    (ℏ κ potential : ℝ) (ψ ψxx : ℂ) :
    probabilityDensityTimeDerivativeValue ψ
        (schrodingerTimeDerivativeValue ℏ κ potential ψ ψxx) +
      probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx = 0 := by
  simp [probabilityDensityTimeDerivativeValue, schrodingerTimeDerivativeValue,
    probabilityCurrentDivergenceValue1D]
  ring

/-- Solve the pointwise Schrödinger equation for its time derivative when `ℏ ≠ 0`. -/
theorem schrodingerTimeDerivativeValue_eq_of_equation
    (ℏ κ potential : ℝ) (ψ ψt ψxx : ℂ) (hℏ : ℏ ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt = -(κ : ℂ) * ψxx + (potential : ℂ) * ψ) :
    ψt = schrodingerTimeDerivativeValue ℏ κ potential ψ ψxx := by
  have hℏc : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  calc
    ψt = (-Complex.I / (ℏ : ℂ)) * (Complex.I * (ℏ : ℂ) * ψt) := by
      field_simp [hℏc]
      simp [Complex.I_sq]
    _ = (-Complex.I / (ℏ : ℂ)) * (-(κ : ℂ) * ψxx + (potential : ℂ) * ψ) := by
      rw [hschrodinger]
    _ = schrodingerTimeDerivativeValue ℏ κ potential ψ ψxx := by
      simp [schrodingerTimeDerivativeValue]
      ring

/-- Pointwise continuity balance derived directly from the nonrelativistic Schrödinger equation with
a real scalar potential. -/
theorem probability_continuity_balance_of_schrodinger
    (ℏ κ potential : ℝ) (ψ ψt ψxx : ℂ) (hℏ : ℏ ≠ 0)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt = -(κ : ℂ) * ψxx + (potential : ℂ) * ψ) :
    probabilityDensityTimeDerivativeValue ψ ψt +
      probabilityCurrentDivergenceValue1D ℏ κ ψ ψxx = 0 := by
  rw [schrodingerTimeDerivativeValue_eq_of_equation ℏ κ potential ψ ψt ψxx hℏ hschrodinger]
  exact probability_continuity_balance_solved ℏ κ potential ψ ψxx

/-- One-dimensional pointwise continuity equation for differentiable time and space slices of a
wavefunction.

The two supplied functions represent the time slice through a fixed spatial point and the spatial
slice at a fixed time. `hsame` identifies their value at the spacetime point under consideration.
No `L²` completion or unbounded-operator assertion is used. -/
theorem oneDimensional_schrodinger_continuity
    (ℏ κ potential : ℝ) (hℏ : ℏ ≠ 0)
    {ψTime ψSpace ψx : ℝ → ℂ} {ψt ψxx : ℂ} {t x : ℝ}
    (hsame : ψTime t = ψSpace x)
    (htime : HasDerivAt ψTime ψt t)
    (hspace : HasDerivAt ψSpace (ψx x) x)
    (hspaceDerivative : HasDerivAt ψx ψxx x)
    (hschrodinger :
      Complex.I * (ℏ : ℂ) * ψt =
        -(κ : ℂ) * ψxx + (potential : ℂ) * ψSpace x) :
    deriv (fun s => probabilityDensityValue (ψTime s)) t +
      deriv (fun y => probabilityCurrentValue1D ℏ κ (ψSpace y) (ψx y)) x = 0 := by
  rw [(hasDerivAt_probabilityDensityValue htime).deriv,
    (hasDerivAt_probabilityCurrentValue1D ℏ κ hspace hspaceDerivative).deriv]
  rw [hsame]
  exact probability_continuity_balance_of_schrodinger
    ℏ κ potential (ψSpace x) ψt ψxx hℏ hschrodinger

/-- Charge density obtained by multiplying probability density by the particle charge. -/
def chargeDensityValue (q : ℝ) (ψ : ℂ) : ℂ :=
  (q : ℂ) * probabilityDensityValue ψ

/-- Charge current obtained by multiplying probability current by the particle charge. -/
def chargeCurrentValue1D (q ℏ κ : ℝ) (ψ ψx : ℂ) : ℂ :=
  (q : ℂ) * probabilityCurrentValue1D ℏ κ ψ ψx

/-- Probability-current balance immediately implies charge-current balance. -/
theorem charge_continuity_balance_of_probability
    (q densityTimeDerivative currentDivergence : ℂ)
    (hcontinuity : densityTimeDerivative + currentDivergence = 0) :
    q * densityTimeDerivative + q * currentDivergence = 0 := by
  rw [← mul_add, hcontinuity, mul_zero]

end
end Continuum
end QuantumTheory
