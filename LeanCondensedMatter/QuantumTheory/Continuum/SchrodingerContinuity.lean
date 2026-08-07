import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
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

namespace QuantumTheory
namespace Continuum

noncomputable section

/-- Pointwise probability density `|ψ|²`, written in real coordinates. -/
def probabilityDensityValue (ψ : ℂ) : ℝ :=
  ψ.re ^ 2 + ψ.im ^ 2

/-- Pointwise one-dimensional probability current for kinetic coefficient `κ`.

This is `(2κ / ℏ) Im (star ψ * ψₓ)`, expanded into real coordinates. -/
def probabilityCurrentValue1D (ℏ κ : ℝ) (ψ ψx : ℂ) : ℝ :=
  (2 * κ / ℏ) * (ψ.re * ψx.im - ψ.im * ψx.re)

/-- The value obtained by differentiating probability density in time. -/
def probabilityDensityTimeDerivativeValue (ψ ψt : ℂ) : ℝ :=
  2 * (ψ.re * ψt.re + ψ.im * ψt.im)

/-- The value obtained by differentiating the one-dimensional probability current in space. -/
def probabilityCurrentDivergenceValue1D (ℏ κ : ℝ) (ψ ψxx : ℂ) : ℝ :=
  (2 * κ / ℏ) * (ψ.re * ψxx.im - ψ.im * ψxx.re)

private theorem hasDerivAt_re
    {ψ : ℝ → ℂ} {ψ' : ℂ} {x : ℝ} (hψ : HasDerivAt ψ ψ' x) :
    HasDerivAt (fun y => (ψ y).re) ψ'.re x := by
  simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hψ

private theorem hasDerivAt_im
    {ψ : ℝ → ℂ} {ψ' : ℂ} {x : ℝ} (hψ : HasDerivAt ψ ψ' x) :
    HasDerivAt (fun y => (ψ y).im) ψ'.im x := by
  simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hψ

/-- A differentiable complex wave amplitude has the expected real density derivative. -/
theorem hasDerivAt_probabilityDensityValue
    {ψ : ℝ → ℂ} {ψt : ℂ} {t : ℝ} (hψ : HasDerivAt ψ ψt t) :
    HasDerivAt (fun s => probabilityDensityValue (ψ s))
      (probabilityDensityTimeDerivativeValue (ψ t) ψt) t := by
  have hre := hasDerivAt_re hψ
  have him := hasDerivAt_im hψ
  convert (hre.mul hre).add (him.mul him) using 1 <;>
    simp [probabilityDensityValue, probabilityDensityTimeDerivativeValue] <;> ring

/-- Differentiating the standard one-dimensional current cancels the two mixed first-derivative
terms, leaving only the second spatial derivative. -/
theorem hasDerivAt_probabilityCurrentValue1D
    (ℏ κ : ℝ) {ψ ψx : ℝ → ℂ} {ψxx : ℂ} {x : ℝ}
    (hψ : HasDerivAt ψ (ψx x) x) (hψx : HasDerivAt ψx ψxx x) :
    HasDerivAt (fun y => probabilityCurrentValue1D ℏ κ (ψ y) (ψx y))
      (probabilityCurrentDivergenceValue1D ℏ κ (ψ x) ψxx) x := by
  have hψre := hasDerivAt_re hψ
  have hψim := hasDerivAt_im hψ
  have hψxre := hasDerivAt_re hψx
  have hψxim := hasDerivAt_im hψx
  have hbracket := (hψre.mul hψxim).sub (hψim.mul hψxre)
  convert hbracket.const_mul (2 * κ / ℏ) using 1 <;>
    simp [probabilityCurrentValue1D, probabilityCurrentDivergenceValue1D] <;> ring

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
end QuantumTheory
